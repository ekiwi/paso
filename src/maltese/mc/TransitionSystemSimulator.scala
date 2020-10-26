// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.mc

import maltese.smt
import treadle.vcd

import scala.collection.mutable

class TransitionSystemSimulator(sys: TransitionSystem, val maxMemVcdSize: Int = 128, printUpdates: Boolean = false) {
  private val (bvStates, arrayStates) = sys.states.partition(s => s.sym.isInstanceOf[smt.BVExpr])
  private val (bvSignals, arraySignals) = sys.signals.partition(s => s.e.isInstanceOf[smt.BVExpr])

  //
  private val allArrays =(arrayStates.map(_.sym) ++ arraySignals.map(_.sym)).map(_.asInstanceOf[smt.ArraySymbol])
  private val allBV = (sys.inputs ++ bvStates.map(_.sym) ++ bvSignals.map(_.sym)).map(_.asInstanceOf[smt.BVSymbol])

  // mutable state indexing
  private val bvNameToIndex = allBV.map(_.name).zipWithIndex.toMap
  private val arrayNameToIndex = allArrays.map(_.name).zipWithIndex.toMap

  // mutable state
  private val data = new mutable.ArraySeq[BigInt](bvNameToIndex.size)
  private val memories = new mutable.ArraySeq[Memory](arrayNameToIndex.size)

  // vcd dumping
  private var vcdWriter: Option[vcd.VCD] = None
  private val observedMemories =
    arrayStates.map(_.sym.asInstanceOf[smt.ArraySymbol]).filter(a => arrayDepth(a.indexWidth) <= maxMemVcdSize)


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

  private def eval(expr: smt.BVExpr): BigInt = {
    val value = expr match {
      case smt.BVLiteral(value, _) => value
      case smt.BVSymbol(name, _) =>
        val value = data(bvNameToIndex(name))
        assert(value != null, s"Trying to read uninitialized symbol $name!")
        value
      case smt.BVExtend(e, by, signed) => smt.SMTExprEval.doBVExtend(eval(e), e.width, by, signed)
      case smt.BVSlice(e, hi, lo) => smt.SMTExprEval.doBVSlice(eval(e), hi, lo)
      case smt.BVNot(e) => smt.SMTExprEval.doBVNot(eval(e), e.width)
      case smt.BVNegate(e) => smt.SMTExprEval.doBVNegate(eval(e), e.width)
      case smt.BVEqual(a, b) => smt.SMTExprEval.doBVEqual(eval(a), eval(b))
      case smt.BVComparison(op, a, b, signed) => smt.SMTExprEval.doBVCompare(op, eval(a), eval(b), a.width, signed)
      case smt.BVOp(op, a, b) => smt.SMTExprEval.doBVOp(op, eval(a), eval(b), a.width)
      case smt.BVConcat(a, b) => smt.SMTExprEval.doBVConcat(eval(a), eval(b), bWidth = b.width)
      case smt.ArrayRead(array, index) => evalArray(array).read(eval(index))
      case smt.BVIte(cond, tru, fals) =>
        val c = eval(cond)
        assert(c == 0 || c == 1)
        if(c == 1) { eval(tru) } else { eval(fals) }
      case smt.BVSelect(_) => throw new NotImplementedError("BVSelect")
      case smt.ArrayEqual(a, b) => if(evalArray(a).data == evalArray(b).data) BigInt(1) else BigInt(0)
    }
    value
  }

  private def evalArray(expr: smt.ArrayExpr): Memory = expr match {
    case s : smt.ArraySymbol => memories(arrayNameToIndex(s.name))
    case smt.ArrayConstant(e, indexWidth) =>
      val value = eval(e)
      Memory(Seq.fill(arrayDepth(indexWidth))(value))
    case smt.ArrayStore(array, index, data) =>
      evalArray(array).write(eval(index), eval(data))
    case smt.ArrayIte(cond, tru, fals) =>
      val c = eval(cond)
      assert(c == 0 || c == 1)
      if(c == 1) { evalArray(tru) } else { evalArray(fals) }
    case other => throw new RuntimeException(s"Unsupported array expression $other")
  }

  private def arrayDepth(indexWidth: Int): Int = (BigInt(1) << indexWidth).toInt

  private def printData(): Unit = {
    println("Inputs:")
    sys.inputs.foreach(i => println(s"${i.name}: ${data(bvNameToIndex(i.name))}"))
    println("Registers:")
    bvStates.foreach(s => println(s"${s.sym}: ${data(bvNameToIndex(s.sym.name))}"))
    println("TODO: memories")
  }

  def init(regInit: Map[Int, BigInt], memInit: Map[Int, Seq[(BigInt, BigInt)]], withVcd: Boolean) = {
    // initialize vcd
    vcdWriter = if(!withVcd) None else {
      val vv = vcd.VCD(sys.name)
      vv.addWire("Step", 64)
      allBV.foreach(s => vv.addWire(s.name, s.width))
      observedMemories.foreach { m =>
        val depth = arrayDepth(m.indexWidth)
        (0 to depth.toInt).foreach(a => vv.addWire(s"${m.name}.$a", m.dataWidth))
      }
      Some(vv)
    }

    // initialize registers and memories in order (this ensures that they are topologically sorted by their init dependencies)
    sys.states.zipWithIndex.foreach { case (state, ii) =>
      if(arrayNameToIndex.contains(state.name)) {
        // init memory
        val value = state.init match {
          case Some(init) => evalArray(init.asInstanceOf[smt.ArrayExpr])
          case None =>
            val depth = arrayDepth(state.sym.asInstanceOf[smt.ArraySymbol].indexWidth)
            if(memInit.contains(ii)) {
              writesToMemory(depth, memInit(ii))
            } else {
              println(s"WARN: Initial value for ${state.sym} ($ii) is missing!")
              Memory(randomSeq(depth))
            }
        }
        memories(arrayNameToIndex(state.name)) = value
      } else {
        // init register
        val value = state.init match {
          case Some(init) => eval(init.asInstanceOf[smt.BVExpr])
          case None => regInit(ii)
        }
        data(bvNameToIndex(state.name)) = value
      }
    }
  }

  private def symbolsToString(symbols: Iterable[smt.SMTSymbol]): Iterable[String] = {
    symbols.collect{ case s: smt.BVSymbol => s }.filter(s => bvNameToIndex.contains(s.name))
      .map(sym => s"$sym := ${data(bvNameToIndex(sym.name))}")
  }

  def step(index: Int, inputs: Map[Int, BigInt], expectedBad: Option[Set[Int]] = None): Unit = {
    vcdWriter.foreach(_.wireChanged("Step", index))

    if(printUpdates) println(s"\nSTEP ${index}")

    // dump state
    vcdWriter.foreach{v =>
      bvStates.foreach{ state => v.wireChanged(state.name, data(bvNameToIndex(state.name))) }
      observedMemories.foreach{ mem =>
        val depth = arrayDepth(mem.indexWidth)
        val array = memories(arrayNameToIndex(mem.name))
        (0 to depth.toInt).foreach(a => v.wireChanged(s"${mem.name}.${a}", array.read(a)))
      }
    }

    // apply inputs
    sys.inputs.zipWithIndex.foreach{ case (input, ii) =>
      val value = inputs(ii) // TODO: deal with missing inputs
      data(ii) = value
      vcdWriter.foreach(_.wireChanged(input.name, value))
      if(printUpdates) println(s"I: ${input.name} <- $value")
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