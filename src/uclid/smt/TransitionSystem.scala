/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2020. The Regents of the University of California
 *
 * All Rights Reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from this
 * software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Author: Kevin Laeufer <laeufer@cs.berkeley.edu>
 *
 */

package uclid.smt

import scala.collection.mutable

case class State(sym: Symbol, init: Option[Expr] = None, next: Option[Expr]= None)
case class TransitionSystem(name: Option[String], inputs: Seq[Symbol], states: Seq[State],
                            outputs: Seq[Tuple2[String,Expr]] = Seq(),
                            constraints: Seq[Expr] = Seq(), bad: Seq[Expr] = Seq(), fair: Seq[Expr] = Seq()) {
  private def disjunction(props: Seq[Expr]): Seq[Expr] = if(props.isEmpty) {Seq()} else {
    Seq(props.reduce{ (a,b) => OperatorApplication(DisjunctionOp, List(a, b)) })
  }
  // ensures that the number of bad states is 1 or 0
  def unifyProperties(): TransitionSystem = {
    this.copy(bad = disjunction(this.bad))
  }
  /* ensures that states are ordered by the dependencies in their init expressions */
  def sortStatesByInitDependencies(): TransitionSystem = {
    val stateSymbols = states.map(_.sym).toSet
    val dependencies = states.map { st =>
      st.sym -> st.init.toSeq.flatMap(Context.findSymbols).toSet.intersect(stateSymbols).diff(Set(st.sym))
    }.toMap
    val dependencyGraph = firrtl.graph.DiGraph(dependencies).reverse
    val stateOrder = dependencyGraph.linearize
    val stateSymToState = states.map{st => st.sym -> st}.toMap
    this.copy(states = stateOrder.map(stateSymToState))
  }
}

trait ModelCheckResult {
  def isFail: Boolean
  def isSuccess: Boolean = !isFail
}
case class ModelCheckSuccess() extends ModelCheckResult { override def isFail: Boolean = false }
case class ModelCheckFail(witness: Witness) extends ModelCheckResult { override def isFail: Boolean = true }

case class Witness(failedBad: Seq[Int], regInit: Map[Int, BigInt], memInit: Map[Int, Seq[(BigInt, BigInt)]], inputs: Seq[Map[Int, BigInt]])

class TransitionSystemSimulator(sys: TransitionSystem) {
  private val inputs = sys.inputs.zipWithIndex.map{ case (input, index) => index -> input }
  private val stateOffset = inputs.size
  private val states = sys.states.zipWithIndex.map{ case (state, index) => index -> state.sym}
  private val outputOffset = stateOffset + states.size
  private val outputs = sys.outputs.zipWithIndex.map{ case ((name, expr), index) => index -> Symbol(name, expr.typ) }


  private val regStates = sys.states.zipWithIndex.filter(!_._1.sym.typ.isArray)
  private val memStates = sys.states.zipWithIndex.filter(_._1.sym.typ.isArray)
  private val memCount = memStates.size

  private val data = new mutable.ArraySeq[BigInt](inputs.size + states.size + outputs.size)
  private val memories = new mutable.ArraySeq[Memory](memCount)
  private val memStateIdToArrayIndex = memStates.map(_._2).zipWithIndex.toMap
  private val memSymbolToArrayIndex = memStates.map{ case (state, i) => state.sym -> memStateIdToArrayIndex(i) }.toMap
  private val bvSymbolToDataIndex : Map[Symbol, Int] =
    (inputs.map{ case (i, sym) => sym -> i} ++ states.map{ case (i, sym) => sym -> (i + stateOffset) }
      ++ outputs.map{ case (i, sym) => sym -> (i + outputOffset) }).toMap

  private case class Memory(data: Seq[BigInt]) {
    def depth: Int = data.size
    def write(index: BigInt, value: BigInt): Memory = {
      assert(index >= 0 && index < depth, s"index ($index) needs to be non-negative smaller than the depth ($depth)!")
      Memory(data.updated(index.toInt, value))
    }
    def read(index: BigInt): BigInt = {
      assert(index >= 0 && index < depth, s"index ($index) needs to be non-negative smaller than the depth ($depth)!")
      data(index.toInt)
    }
  }
  private def randomSeq(depth: Int): Seq[BigInt] = {
    val r = scala.util.Random
    (0 to depth).map( _ => BigInt(r.nextLong()))
  }
  private def writesToMemory(depth: Int, writes: Iterable[(BigInt, BigInt)]): Memory =
    writes.foldLeft(Memory(randomSeq(depth))){ case(mem, (index, value)) => mem.write(index, value)}

  private def eval(expr: Expr): BigInt = {
    val value = expr match {
      case s: Symbol => data(bvSymbolToDataIndex(s))
      case OperatorApplication(EqualityOp, List(a, b)) if a.typ.isArray => arrayEq(a, b)
      case OperatorApplication(InequalityOp, List(a, b)) if a.typ.isArray => arrayIneq(a, b)
      case OperatorApplication(op, List(a)) => BitVectorAndBoolSemantics.unary(op, eval(a))
      case OperatorApplication(op, List(a, b)) => BitVectorAndBoolSemantics.binary(op, eval(a), eval(b))
      case OperatorApplication(op, List(a,b,c)) => BitVectorAndBoolSemantics.ternary(op, eval(a), eval(b), eval(c))
      case BitVectorLit(value, _) => value
      case BooleanLit(value) => if(value) BigInt(1) else BigInt(0)
      case ArraySelectOperation(array, List(index)) => evalArray(array).read(eval(index))
      case other => throw new RuntimeException(s"Unsupported expression $other")
    }
    // println(s"$expr = $value")
    value
  }
  private def arrayEq(a: Expr, b: Expr): BigInt = if(evalArray(a).data == evalArray(b).data) BigInt(1) else BigInt(0)
  private def arrayIneq(a: Expr, b: Expr): BigInt = if(evalArray(a).data != evalArray(b).data) BigInt(1) else BigInt(0)

  private def evalArray(expr: Expr): Memory = expr match {
    case s : Symbol => memories(memSymbolToArrayIndex(s))
    case ConstArray(expr, arrTyp) =>
      val value = eval(expr)
      Memory(Seq.fill(arrayDepth(arrTyp))(value))
    case ArrayStoreOperation(array, List(index), value) =>
      evalArray(array).write(eval(index), eval(value))
    case OperatorApplication(ITEOp, List(cond, tru, fals)) => if(eval(cond) == 1) evalArray(tru) else evalArray(fals)
    case other => throw new RuntimeException(s"Unsupported array expression $other")
  }

  private def arrayDepth(arrayType: Type): Int = {
    val addrWidth = arrayType.asInstanceOf[ArrayType].inTypes.head.asInstanceOf[BitVectorType].width
    ((BigInt(1) << addrWidth) - 1).toInt
  }

  private def printData(): Unit = {
    println("Inputs:")
    inputs.foreach { case (i, symbol) => println(s"${symbol}: ${data(i)}") }
    println("Registers:")
    regStates.foreach{ case (state, i) => println(s"${state.sym}: ${data(i + stateOffset)}")}
    println("TODO: memories")
  }

  def init(regInit: Map[Int, BigInt], memInit: Map[Int, Seq[(BigInt, BigInt)]]) = {
    // initialize registers
    regStates.foreach { case (state, ii) =>
      val value = state.init match {
        case Some(init) => eval(init)
        case None => regInit(ii)
      }
      data(ii + stateOffset) = value
    }

    // initialize memories
    memStates.foreach { case (state, ii) =>
      val value = state.init match {
        case Some(init) => evalArray(init)
        case None =>
          if(memInit.contains(ii)) {
            writesToMemory(arrayDepth(state.sym.typ), memInit(ii))
          } else {
            println(s"WARN: Initial value for ${state.sym} ($ii) is missing!")
            Memory(randomSeq(arrayDepth(state.sym.typ)))
          }
      }
      memories(memStateIdToArrayIndex(ii)) = value
    }
  }

  private def symbolsToString(symbols: Iterable[Symbol]): Iterable[String] =
    symbols.filter(!_.typ.isArray).map{sym => s"$sym := ${data(bvSymbolToDataIndex(sym))}"}

  def step(inputs: Map[Int, BigInt]): Unit = {
    // apply inputs
    inputs.foreach{ case(ii, value) => data(ii) = value }

    // calculate next states
    val newRegValues = regStates.map { case (state, ii) =>
      val value = state.next match {
        case Some(next) => eval(next)
        case None => throw new NotImplementedError(s"State $state without a next function is not supported")
      }
      (ii, value)
    }

    val newMemValues = memStates.map { case (state, ii) =>
      val value = state.next match {
        case Some(next) => evalArray(next)
        case None => throw new NotImplementedError(s"State $state without a next function is not supported")
      }
      (ii, value)
    }

    // evaluate outputs
    val newOutputs = sys.outputs.zipWithIndex.map { case ((name, expr), ii) =>
      val value = eval(expr)
      // println(s"Output: $name := $value")
      (ii, value)
    }
    // update outputs (constraints and bad states could depend on the new value)
    newOutputs.foreach{ case (ii, value) => data(ii + outputOffset) = value }

    // make sure constraints are not violated
    sys.constraints.foreach { expr =>
      val holds = eval(expr)
      assert(holds == 0 || holds == 1, s"Constraint $expr returned invalid value when evaluated: $holds")
      if(eval(expr) == 0) {
        println(s"ERROR: Constraint $expr was violated!")
        symbolsToString(Context.findSymbols(expr)).foreach(println)
        //printData()
        throw new RuntimeException("Violated constraint!")
      }
    }

    // evaluate safety properties
    val failed = sys.bad.zipWithIndex.map { case (expr, ii) => (ii, eval(expr)) }.filter(_._2 != 0).map(_._1)
    def failedMsg(p: Int) = {
      val expr = sys.bad(p)
      val syms = symbolsToString(Context.findSymbols(expr)).mkString(", ")
      s"b$p: $expr ($syms)"
    }
    assert(failed.isEmpty, s"Failed (${failed.size}) properties:\n${failed.map(failedMsg).mkString("\n")}")

    // update state
    newRegValues.foreach{ case (ii, value) => data(ii + stateOffset) = value }
    newMemValues.foreach{ case (ii, value) => memories(memStateIdToArrayIndex(ii)) = value }
  }

  def run(witness: Witness): Unit = {
    init(witness.regInit, witness.memInit)
    witness.inputs.zipWithIndex.foreach { case(inputs, index) =>
      //println(s"Step($index)")
      step(inputs)
    }
  }
}


object BitVectorAndBoolSemantics {
  private def mask(w: Int): BigInt = (BigInt(1) << w) - 1
  private def isPositive(value: BigInt, w: Int) = (value & mask(w-1)) == value
  private def isNegative(value: BigInt, w: Int) = !isPositive(value, w)
  private def bool(b: Boolean): BigInt = if(b) BigInt(1) else BigInt(0)
  private def flipBits(value: BigInt, w: Int) = ~value & mask(w)
  def unary(op: Operator, a: BigInt): BigInt = op match {
    case BVZeroExtOp(_, _) => a
    case BVSignExtOp(w, e) => if(isPositive(a, w-e)) a else a | (mask(e) << (w-e))
    case BVExtractOp(hi, lo) => (a >> lo) & mask(hi - lo + 1)
    case BVNotOp(w) => flipBits(a, w)
    case NegationOp => flipBits(a, 1)
    case other => throw new RuntimeException(s"Unsupported unary operation $other.")
  }
  def binary(op: Operator, a: BigInt, b: BigInt): BigInt = op match {
    case EqualityOp | IffOp => bool(a == b)
    case InequalityOp => bool(a != b)
    case BVLEUOp(_) => bool(a <= b)
    case BVLTUOp(_) => bool(a < b)
    case BVGEUOp(_) => bool(a >= b)
    case BVGTUOp(_) => bool(a > b)
    case BVAddOp(w) => (a + b) & mask(w)
    case BVSubOp(w) => (a + flipBits(b, w) + 1) & mask(w)
    case BVAndOp(_) | ConjunctionOp => a & b
    case BVOrOp(_) | DisjunctionOp => a | b
    case BVXorOp(_) => a ^ b
    case ImplicationOp => flipBits(a, 1) | b
    case other => throw new RuntimeException(s"Unsupported binary operation $other.")
  }
  def ternary(op: Operator, a: BigInt, b: BigInt, c: BigInt): BigInt = op match {
    case ITEOp => if(a == 1) b else if(a == 0) c else throw new RuntimeException(s"Invalid value for bool: $a")
    case other => throw new RuntimeException(s"Unsupported ternary operation $other.")
  }
}