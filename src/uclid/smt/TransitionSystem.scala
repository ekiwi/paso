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

import paso.chisel.SMTSimplifier
import uclid.vcd

import scala.collection.mutable

case class State(sym: Symbol, init: Option[Expr] = None, next: Option[Expr]= None)
case class TransitionSystem(name: Option[String], inputs: Seq[Symbol], states: Seq[State],
                            outputs: Seq[Tuple2[String,Expr]] = Seq(),
                            constraints: Seq[Expr] = Seq(), bad: Seq[Expr] = Seq(), fair: Seq[Expr] = Seq()) {
  private def disjunction(props: Seq[Expr]): Seq[Expr] = if(props.isEmpty) {Seq()} else {
    Seq(props.reduce{ (a,b) => OperatorApplication(DisjunctionOp, List(a, b)) })
  }
  private def conjunction(props: Seq[Expr]): Seq[Expr] = if(props.isEmpty) {Seq()} else {
    Seq(props.reduce{ (a,b) => OperatorApplication(ConjunctionOp, List(a, b)) })
  }
  // ensures that the number of bad states is 1 or 0
  def unifyProperties(): TransitionSystem = {
    this.copy(bad = disjunction(this.bad))
  }
  // ensures that the number of constraints is 1 or 0
  def unifyConstraints(): TransitionSystem = {
    this.copy(constraints = conjunction(this.constraints))
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

object TransitionSystem {
  def getAllSymbols(sys: TransitionSystem): Seq[Symbol] = {
    sys.inputs ++ sys.outputs.map(o => Symbol(o._1, o._2.typ)) ++ sys.states.map(_.sym)
  }
  def merge(name: String, a: TransitionSystem, b: TransitionSystem): TransitionSystem = {
    val aSyms = getAllSymbols(a).map(_.id).toSet
    getAllSymbols(b).foreach(s => assert(!aSyms.contains(s.id), s"Name collision! $s appears both in ${a.name} and ${b.name}"))
    TransitionSystem(
      name = Some(name),
      inputs = a.inputs ++ b.inputs,
      states = a.states ++ b.states,
      outputs = a.outputs ++ b.outputs,
      constraints = a.constraints ++ b.constraints,
      bad = a.bad ++ b.bad,
      fair = a.fair ++ b.fair
    )
  }
  def merge(original: TransitionSystem, others: Iterable[TransitionSystem]): TransitionSystem = {
    val name = original.name.get
    others.foldLeft(original)(merge(name, _, _))
  }
}

trait ModelCheckResult {
  def isFail: Boolean
  def isSuccess: Boolean = !isFail
}
case class ModelCheckSuccess() extends ModelCheckResult { override def isFail: Boolean = false }
case class ModelCheckFail(witness: Witness) extends ModelCheckResult { override def isFail: Boolean = true }

trait IsModelChecker {
  val name: String
  val supportsUF: Boolean = false
  val supportsQuantifiers: Boolean = false
  def check(sys: TransitionSystem, kMax: Int = -1, fileName: Option[String] = None, defined: Seq[DefineFun] = Seq(), uninterpreted: Seq[Symbol] = Seq()): ModelCheckResult
}

case class Witness(failedBad: Seq[Int], regInit: Map[Int, BigInt], memInit: Map[Int, Seq[(BigInt, BigInt)]], inputs: Seq[Map[Int, BigInt]])

class TransitionSystemSimulator(sys: TransitionSystem, val maxMemVcdSize: Int = 128, functionDefinitions: Seq[DefineFun] = Seq(), printUpdates: Boolean = false) {
  private val inputs = sys.inputs.zipWithIndex.map{ case (input, index) => index -> input }
  private val stateOffset = inputs.size
  private val states = sys.states.zipWithIndex.map{ case (state, index) => index -> state.sym}
  private val outputOffset = stateOffset + states.size
  private val outputs = sys.outputs.zipWithIndex.map{ case ((name, expr), index) => index -> Symbol(name, expr.typ) }
  private val regStates = sys.states.zipWithIndex.filter(!_._1.sym.typ.isArray)
  private val memStates = sys.states.zipWithIndex.filter(_._1.sym.typ.isArray)
  private val allStates = sys.states.zipWithIndex
  private val memCount = memStates.size

  // mutable state
  private val data = new mutable.ArraySeq[BigInt](inputs.size + states.size + outputs.size)
  private val memories = new mutable.ArraySeq[Memory](memCount)

  // mutable state indexing
  private val memStateIdToArrayIndex = memStates.map(_._2).zipWithIndex.toMap
  private val memSymbolToArrayIndex = memStates.map{ case (state, i) => state.sym -> memStateIdToArrayIndex(i) }.toMap
  private val bvSymbolToDataIndex : Map[Symbol, Int] =
    (inputs.map{ case (i, sym) => sym -> i} ++ regStates.map{ case (state, i) => state.sym -> (i + stateOffset) }
      ++ outputs.map{ case (i, sym) => sym -> (i + outputOffset) }).toMap
  private val dataIndexToName: Map[Int, String] = bvSymbolToDataIndex.map{ case (symbol, i) => i -> symbol.id}

  // vcd dumping
  private var vcdWriter: Option[vcd.VCD] = None
  private val observedMemories = memSymbolToArrayIndex.filter{case (Symbol(_, typ), _) => getDepthAndWidth(typ)._1 <= maxMemVcdSize}

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
  private def randomBits(bits: Int): BigInt = BigInt(bits, scala.util.Random)
  private def randomSeq(depth: Int): Seq[BigInt] = {
    val r = scala.util.Random
    (0 to depth).map( _ => BigInt(r.nextLong()))
  }
  private def writesToMemory(depth: Int, writes: Iterable[(BigInt, BigInt)]): Memory =
    writes.foldLeft(Memory(randomSeq(depth))){ case(mem, (index, value)) => mem.write(index, value)}

  private val functionResults = mutable.HashMap[String, BigInt]()
  private def evalUninterpretedFunctionCall(foo: Symbol, args: Seq[BigInt]): BigInt = {
    val id = foo.id + "(" + args.mkString(";") + ")"
    val res = functionResults.getOrElseUpdate(id, randomBits(getWidth(foo.typ.asInstanceOf[MapType].outType)))
    res
  }
  private val tmpSymbols = mutable.HashMap[Symbol, BigInt]()
  private def evalFunctionCall(foo: Symbol, args: Seq[BigInt]): BigInt = {
    functionDefinitions.find(_.id == foo) match {
      case None => evalUninterpretedFunctionCall(foo, args)
      case Some(d) =>
        d.args.zip(args).foreach{ case (sym, value) => tmpSymbols(sym) = value }
        eval(d.e)
    }
  }

  private def eval(expr: Expr): BigInt = {
    val value = expr match {
      case s: Symbol =>
        bvSymbolToDataIndex.get(s).map { index =>
          val value = data(index)
          assert(value != null, s"Trying to read uninitialized symbol $s!")
          value
        }.getOrElse {
          tmpSymbols(s)
        }
      case OperatorApplication(EqualityOp, List(a, b)) if a.typ.isArray => arrayEq(a, b)
      case OperatorApplication(InequalityOp, List(a, b)) if a.typ.isArray => arrayIneq(a, b)
      case OperatorApplication(BVConcatOp(_), List(a, b)) => BitVectorAndBoolSemantics.concat(eval(a), eval(b), b.typ.asInstanceOf[BitVectorType].width)
      case OperatorApplication(op, List(a)) => BitVectorAndBoolSemantics.unary(op, eval(a))
      case OperatorApplication(op, List(a, b)) => BitVectorAndBoolSemantics.binary(op, eval(a), eval(b))
      case OperatorApplication(op, List(a,b,c)) => BitVectorAndBoolSemantics.ternary(op, eval(a), eval(b), eval(c))
      case BitVectorLit(value, _) => value
      case BooleanLit(value) => if(value) BigInt(1) else BigInt(0)
      case ArraySelectOperation(array, List(index)) => evalArray(array).read(eval(index))
      case FunctionApplication(e, args) => evalFunctionCall(e.asInstanceOf[Symbol], args.map(eval))
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
    ((BigInt(1) << addrWidth)).toInt
  }

  private def printData(): Unit = {
    println("Inputs:")
    inputs.foreach { case (i, symbol) => println(s"${symbol}: ${data(i)}") }
    println("Registers:")
    regStates.foreach{ case (state, i) => println(s"${state.sym}: ${data(i + stateOffset)}")}
    println("TODO: memories")
  }

  private def getWidth(typ: Type): Int = typ match { case BoolType => 1 case BitVectorType(w) => w }
  private def getDepthAndWidth(typ: Type): (BigInt, Int) = typ match {
    case ArrayType(List(BitVectorType(w0)), BitVectorType(w1)) => ((BigInt(1) << w0) - 1, w1)
    case ArrayType(List(BitVectorType(w0)), BoolType) => ((BigInt(1) << w0) - 1, 1)
  }
  def init(regInit: Map[Int, BigInt], memInit: Map[Int, Seq[(BigInt, BigInt)]], withVcd: Boolean) = {
    // initialize vcd
    vcdWriter = if(!withVcd) None else {
      val vv = vcd.VCD(sys.name.getOrElse("Top"))
      vv.addWire("Step", 64)
      bvSymbolToDataIndex.keys.foreach(s => vv.addWire(s.id, getWidth(s.typ)))
      observedMemories.foreach { case(s, _) =>
        val (depth, width) = getDepthAndWidth(s.typ)
        (0 to depth.toInt).foreach(a => vv.addWire(s"${s.id}.${a}", width))
      }
      sys.constraints.zipWithIndex.foreach{ case (_, i) => vv.addWire(s"Constraints.c$i", 1)}
      sys.bad.zipWithIndex.foreach{ case (_, i) => vv.addWire(s"BadStates.b$i", 1)}
      Some(vv)
    }

    // initialize registers and memories in order (this ensures that they are topologically sorted by their init dependencies)
    allStates.foreach { case (state, ii) =>
      if(state.sym.typ.isArray) {
        // init memory
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
      } else {
        // init register
        val value = state.init match {
          case Some(init) => eval(init)
          case None => regInit(ii)
        }
        data(ii + stateOffset) = value
      }
    }
  }

  private def symbolsToString(symbols: Iterable[Symbol]): Iterable[String] =
    symbols.filter(!_.typ.isArray).filter(bvSymbolToDataIndex.contains).map{sym => s"$sym := ${data(bvSymbolToDataIndex(sym))}"}

  def step(index: Int, inputs: Map[Int, BigInt], expectedBad: Option[Set[Int]] = None): Unit = {
    vcdWriter.foreach(_.wireChanged("Step", index))

    if(printUpdates) println(s"\nSTEP ${index}")

    // dump state
    vcdWriter.foreach{v =>
      regStates.foreach{ case (state, i) => v.wireChanged(state.sym.id, data(i + stateOffset)) }
      observedMemories.foreach{ case (sym, ii) =>
        val (depth, _) = getDepthAndWidth(sym.typ)
        (0 to depth.toInt).foreach(a => v.wireChanged(s"${sym.id}.${a}", memories(ii).read(a)))
      }
    }

    // apply inputs
    inputs.foreach{ case(ii, value) =>
      data(ii) = value
      vcdWriter.foreach(_.wireChanged(dataIndexToName(ii), value))
      if(printUpdates) println(s"I: ${dataIndexToName(ii)} <- $value")
    }

    // evaluate outputs
    val newOutputs = sys.outputs.zipWithIndex.map { case ((name, expr), ii) =>
      val value = eval(expr)
      if(printUpdates) println(s"O: $name -> $value")
      (ii, value)
    }
    // update outputs (constraints, bad states and next state functions could depend on the new value)
    newOutputs.foreach{ case (ii, value) =>
      data(ii + outputOffset) = value
      vcdWriter.foreach(_.wireChanged(dataIndexToName(ii + outputOffset), value))
    }

    // calculate next states
    val newRegValues = regStates.map { case (state, ii) =>
      val value = state.next match {
        case Some(next) => eval(next)
        case None => throw new NotImplementedError(s"State $state without a next function is not supported")
      }
      (ii, value)
    }.toVector

    val newMemValues = memStates.map { case (state, ii) =>
      val value = state.next match {
        case Some(next) => evalArray(next)
        case None => throw new NotImplementedError(s"State $state without a next function is not supported")
      }
      (ii, value)
    }.toVector

    // make sure constraints are not violated
    def simpl(e: Expr): Expr = SMTSimplifier.simplify(e) // TODO: this uses code outside of uclid...
    sys.constraints.zipWithIndex.foreach { case (expr, i) =>
      val holds = eval(expr)
      assert(holds == 0 || holds == 1, s"Constraint $expr returned invalid value when evaluated: $holds")
      vcdWriter.foreach(_.wireChanged(s"Constraints.c$i", holds))
      if(eval(expr) == 0) {
        println(s"ERROR: Constraint #$i ${simpl(expr)} was violated!")
        symbolsToString(Context.findSymbols(expr)).foreach(println)
        //printData()
        //throw new RuntimeException("Violated constraint!")
      }
    }

    // evaluate safety properties
    val failed = sys.bad.zipWithIndex.map { case (expr, ii) =>
      val value = eval(expr)
      vcdWriter.foreach(_.wireChanged(s"BadStates.b$ii", value))
      (ii, value)
    }.filter(_._2 != 0).map(_._1)
    def failedMsg(p: Int) = {
      val expr = simpl(sys.bad(p))
      val syms = symbolsToString(Context.findSymbols(expr)).mkString(", ")
      s"b$p: $expr with $syms"
    }
    def failedPropertiesMsg: String = s"Failed (${failed.size}) properties in step #$index:\n${failed.map(failedMsg).mkString("\n")}"
    expectedBad match {
      case None => assert(failed.isEmpty, failedPropertiesMsg)
      case Some(props) =>
        if(!props.subsetOf(failed.toSet)) {
          println(s"In step #$index: Expected properties ${props.map("b"+_).mkString(", ")} to fail, instead ${failed.map("b"+_).mkString(", ")} failed");
        }
        //assert(props.subsetOf(failed.toSet), s"In step #$index: Expected properties ${props.map("b"+_).mkString(", ")} to fail, instead ${failed.map("b"+_).mkString(", ")} failed")
        println(failedPropertiesMsg)
    }

    // increment time
    vcdWriter.foreach(_.incrementTime())

    // update state
    newRegValues.foreach{ case (ii, value) =>
      if(printUpdates) println(s"R: ${dataIndexToName(ii + stateOffset)} <- $value")
      data(ii + stateOffset) = value
    }
    newMemValues.foreach{ case (ii, value) => memories(memStateIdToArrayIndex(ii)) = value }
  }

  def run(witness: Witness, vcdFileName: Option[String] = None): Unit = {
    init(witness.regInit, witness.memInit, withVcd = vcdFileName.nonEmpty)
    witness.inputs.zipWithIndex.foreach { case (inputs, index) =>
      //println(s"Step($index)")
      // on the last step we expect the bad states to be entered
      if (index == witness.inputs.size - 1 && witness.failedBad.nonEmpty) {
        step(index, inputs, Some(witness.failedBad.toSet))
      } else {
        step(index, inputs)
      }
    }
    vcdFileName.foreach { ff =>
      val vv = vcdWriter.get
      vv.wireChanged("Step", witness.inputs.size)
      vv.incrementTime()
      vv.write(ff)
    }
    functionResults.foreach { case (id, res) => println(s"$id --> $res") }
    // functionResults.foreach { case (id, res) => println(s"$id --> $res") }
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
    case BVMulOp(w) => (a * b) & mask(w)
    case BVSubOp(w) => (a + flipBits(b, w) + 1) & mask(w)
    case BVAndOp(_) | ConjunctionOp => a & b
    case BVOrOp(_) | DisjunctionOp => a | b
    case BVXorOp(_) => a ^ b
    case ImplicationOp => flipBits(a, 1) | b
    case other => throw new RuntimeException(s"Unsupported binary operation $other.")
  }
  def concat(a: BigInt, b: BigInt, bWidth: Int): BigInt = {
    a << bWidth | b
  }
  def ternary(op: Operator, a: BigInt, b: BigInt, c: BigInt): BigInt = op match {
    case ITEOp => if(a == 1) b else if(a == 0) c else throw new RuntimeException(s"Invalid value for bool: $a")
    case other => throw new RuntimeException(s"Unsupported ternary operation $other.")
  }
}