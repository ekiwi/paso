// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.mc

import maltese.smt
import maltese.smt.BVSymbol
import treadle.{random, vcd}

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
  private val data = new Array[BigInt](bvNameToIndex.size)
  private val memories = new Array[Memory](arrayNameToIndex.size)

  // quantifier variables
  private val varData = new mutable.HashMap[String, BigInt]()

  // vcd dumping
  private var vcdWriter: Option[vcd.VCD] = None
  private val observedMemories =
    arrayStates.map(_.sym.asInstanceOf[smt.ArraySymbol]).filter(a => arrayDepth(a.indexWidth) <= maxMemVcdSize)

  //
  private val badNameToIndex: Map[String, Int] = sys.signals.filter(_.lbl == IsBad).map(_.name).zipWithIndex.toMap


  private case class Memory(data: Seq[BigInt]) extends smt.ArrayValue {
    def depth: Int = data.size
    def write(index: Option[BigInt], value: BigInt): Memory = {
      index match {
        case None => Memory(Array.fill(depth)(value))
        case Some(ii) =>
          assert(ii >= 0 && ii < depth, s"index ($ii) needs to be non-negative smaller than the depth ($depth)!")
          Memory(data.updated(ii.toInt, value))
      }
    }
    def read(index: BigInt): BigInt = {
      assert(index >= 0 && index < depth, s"index ($index) needs to be non-negative smaller than the depth ($depth)!")
      data(index.toInt)
    }
    def ==(other: smt.ArrayValue): Boolean = {
      assert(other.isInstanceOf[Memory])
      other.asInstanceOf[Memory].data == this.data
    }
  }
  private def randomBits(bits: Int): BigInt = BigInt(bits, scala.util.Random)
  private def randomSeq(depth: Int, bits: Int): Seq[BigInt] = (0 to depth).map( _ => randomBits(bits))

  private def writesToMemory(depth: Int, bits: Int,  writes: Iterable[(Option[BigInt], BigInt)]): Memory =
    writes.foldLeft(Memory(randomSeq(depth, bits))){ case(mem, (index, value)) => mem.write(index, value)}

  private val evalCtx = new smt.SMTEvalCtx {
    override def getBVSymbol(name: String): BigInt = {
      val value = bvNameToIndex.get(name) match {
        case Some(index) => data(index)
        case None => varData(name)
      }
      assert(value != null, s"Trying to read uninitialized symbol $name!")
      value
    }

    override def getArraySymbol(name: String): Memory = memories(arrayNameToIndex(name))

    override def startVariableScope(name: String, value: BigInt): Unit = {
      assert(!varData.contains(name))
      varData(name) = value
    }
    override def endVariableScope(name: String): Unit = {
      varData.remove(name)
    }

    override def constArray(indexWidth: Int, value: BigInt) = {
      Memory(Seq.fill(arrayDepth(indexWidth))(value))
    }
  }

  private val CheckWidths = true
  private def eval(expr: smt.BVExpr): BigInt = {
    val value = smt.SMTExprEval.eval(expr)(evalCtx)
    if(CheckWidths) {
      val mask = (BigInt(1) << expr.width) - 1
      if((value & mask) != value) {
        throw new RuntimeException(s"Failed to evaluate ${expr}!\nvalue $value does not fit into ${expr.width} bits!")
      }
    }
    value
  }
  private def evalArray(expr: smt.ArrayExpr): Memory = smt.SMTExprEval.evalArray(expr)(evalCtx).asInstanceOf[Memory]

  private def arrayDepth(indexWidth: Int): Int = (BigInt(1) << indexWidth).toInt

  private def printData(): Unit = {
    println("Inputs:")
    sys.inputs.foreach(i => println(s"${i.name}: ${data(bvNameToIndex(i.name))}"))
    println("Registers:")
    bvStates.foreach(s => println(s"${s.sym}: ${data(bvNameToIndex(s.sym.name))}"))
    println("TODO: memories")
  }

  def init(regInit: Map[Int, BigInt], memInit: Map[Int, Seq[(Option[BigInt], BigInt)]], withVcd: Boolean) = {
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
            val sym = state.sym.asInstanceOf[smt.ArraySymbol]
            val depth = arrayDepth(sym.indexWidth)
            val bits = sym.dataWidth
            if(memInit.contains(ii)) {
              writesToMemory(depth, bits, memInit(ii))
            } else {
              println(s"WARN: Initial value for ${state.sym} ($ii) is missing!")
              Memory(randomSeq(depth, bits))
            }
        }
        memories(arrayNameToIndex(state.name)) = value
      } else {
        // init register
        val value = state.init match {
          case Some(init) => eval(init.asInstanceOf[smt.BVExpr])
          case None => regInit.get(ii) match {
            case Some(value) => value
            case None =>
              println(s"WARN: Initial value for ${state.sym} ($ii) is missing!")
              randomBits(state.sym.asInstanceOf[BVSymbol].width)
          }
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
        (0 until depth.toInt).foreach(a => v.wireChanged(s"${mem.name}.${a}", array.read(a)))
      }
    }

    // apply inputs
    sys.inputs.zipWithIndex.foreach{ case (input, ii) =>
      val value = inputs(ii) // TODO: deal with missing inputs
      data(ii) = value
      vcdWriter.foreach(_.wireChanged(input.name, value))
      if(printUpdates) println(s"I: ${input.name} <- $value")
    }

    // evaluate signals
    sys.signals.foreach {
      case Signal(name, e: smt.BVExpr, _) =>
        val value = eval(e)
        if(printUpdates) println(s"S: $name -> $value")
        data(bvNameToIndex(name)) = value
        vcdWriter.foreach(_.wireChanged(name, value))
      case Signal(name, e: smt.ArrayExpr, _) =>
        val value = evalArray(e)
        memories(arrayNameToIndex(name)) = value
    }

    // calculate next states
    val newBVState = bvStates.map { state =>
      val value = state.next match {
        case Some(next) => eval(next.asInstanceOf[smt.BVExpr])
        case None => throw new NotImplementedError(s"State $state without a next function is not supported")
      }
      (state.name, value)
    }.toVector

    val newArrayState = arrayStates.map { state =>
      val value = state.next match {
        case Some(next) => evalArray(next.asInstanceOf[smt.ArrayExpr])
        case None => throw new NotImplementedError(s"State $state without a next function is not supported")
      }
      (state.name, value)
    }.toVector

    // make sure constraints are not violated
    def simpl(e: smt.SMTExpr): smt.SMTExpr = smt.SMTSimplifier.simplify(e)
    sys.signals.filter(_.lbl == IsConstraint).foreach { signal =>
      val holds = data(bvNameToIndex(signal.name))
      assert(holds == 0 || holds == 1, s"Constraint ${signal.name} returned invalid value when evaluated: $holds")
      if(holds == 0) {
        println(s"ERROR: Constraint #${signal.name} was violated!")
        //symbolsToString(Context.findSymbols(expr)).foreach(println)
        //printData()
        //throw new RuntimeException("Violated constraint!")
      }
    }

    // check to see if any safety properties failed
    val failed = sys.signals.filter(_.lbl == IsBad).map { signal =>
      (signal.name, data(bvNameToIndex(signal.name)))
    }.filter(_._2 != 0).map(_._1)
    def failedMsg(name: String): String = {
      val expr = simpl(sys.signals.find(_.name == name).get.e)
      //val syms = symbolsToString(Context.findSymbols(expr)).mkString(", ")
      s"$name: $expr"
    }
    def failedPropertiesMsg: String = s"Failed (${failed.size}) properties in step #$index:\n${failed.map(failedMsg).mkString("\n")}"
    expectedBad match {
      case None => assert(failed.isEmpty,  "Unexpected failure!! " + failedPropertiesMsg)
      case Some(props) =>
        val failedSet = failed.map(badNameToIndex(_)).toSet
        if(!props.subsetOf(failedSet)) {
          println(s"In step #$index: Expected properties ${props.map("b"+_).mkString(", ")} to fail, instead ${failed.map("b"+_).mkString(", ")} failed");
        }
        //assert(props.subsetOf(failed.toSet), s"In step #$index: Expected properties ${props.map("b"+_).mkString(", ")} to fail, instead ${failed.map("b"+_).mkString(", ")} failed")
        println(failedPropertiesMsg)
    }

    // increment time
    vcdWriter.foreach(_.incrementTime())

    // update state
    newBVState.foreach{ case (name, value) =>
      if(printUpdates) println(s"R: $name <- $value")
      data(bvNameToIndex(name)) = value
    }
    newArrayState.foreach{ case (name, value) => memories(arrayNameToIndex(name)) = value }
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
  }
}