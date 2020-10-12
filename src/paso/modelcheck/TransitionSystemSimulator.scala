// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.modelcheck

import maltese.smt
import scala.collection.mutable

case class Witness(failedBad: Seq[Int], regInit: Map[Int, BigInt], memInit: Map[Int, Seq[(BigInt, BigInt)]], inputs: Seq[Map[Int, BigInt]])

class TransitionSystemSimulator(sys: smt.TransitionSystem, val maxMemVcdSize: Int = 128, printUpdates: Boolean = false) {
  private val inputs = sys.inputs.zipWithIndex.map{ case (input, index) => index -> input }
  private val stateOffset = inputs.size
  private val states = sys.states.zipWithIndex.map{ case (state, index) => index -> state.sym}
  private val signalOffset = stateOffset + states.size
  private val signals = sys.signals.zipWithIndex.map{ case (s, index) => index -> s.e. }
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
      ++ outputs.map{ case (i, sym) => sym -> (i + signalOffset) }).toMap
  private val dataIndexToName: Map[Int, String] = bvSymbolToDataIndex.map{ case (symbol, i) => i -> symbol.id}

  // vcd dumping
  private var vcdWriter: Option[VCD] = None
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
      val vv = VCD(sys.name)
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
      data(ii + signalOffset) = value
      vcdWriter.foreach(_.wireChanged(dataIndexToName(ii + signalOffset), value))
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
