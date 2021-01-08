// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.mc

import maltese.smt
import maltese.smt.{Comment, DeclareFunction, DeclareUninterpretedSort, DeclareUninterpretedSymbol, DefineFunction, SMTCommand, solvers}

import scala.collection.mutable

case class SMTModelCheckerOptions(checkConstraints: Boolean, checkBadStatesIndividually: Boolean)
object SMTModelCheckerOptions {
  val Default: SMTModelCheckerOptions = SMTModelCheckerOptions(true, true)
  val Performance: SMTModelCheckerOptions = SMTModelCheckerOptions(false, false)
}

/** SMT based bounded model checking as an alternative to dispatching to a btor2 based external solver */
class SMTModelChecker(val solver: smt.Solver, options: SMTModelCheckerOptions = SMTModelCheckerOptions.Performance, printProgress: Boolean = false) extends IsModelChecker {
  override val name: String = "SMTModelChecker with " + solver.name
  override val prefix: String = solver.name
  override val fileExtension: String = ".smt2"
  override val supportsUF: Boolean = true
  override val supportsQuantifiers: Boolean = solver.supportsQuantifiers

  override def check(sys: TransitionSystem, kMax: Int, fileName: Option[String] = None): ModelCheckResult = {
    require(kMax > 0 && kMax <= 2000, s"unreasonable kMax=$kMax")
    if(fileName.nonEmpty) println("WARN: dumping to file is not supported at the moment.")

    val features = TransitionSystem.analyzeFeatures(sys)
    // set correct logic for solver
    val logic = SMTTransitionSystemEncoder.determineLogic(features)
    solver.setLogic(logic)

    // create new context
    solver.push()

    // declare UFs if necessary
    if(features.hasUF) {
      val foos = TransitionSystem.findUFs(sys)
      assert(foos.nonEmpty)
      foos.foreach(solver.runCommand(_))
    }

    // declare/define functions and encode the transition system
    val enc: SMTEncoding = new CompactEncoding(sys)
    enc.defineHeader(solver)
    enc.init(solver)

    val constraints = sys.signals.filter(_.lbl == IsConstraint).map(_.name)
    val bads = sys.signals.filter(_.lbl == IsBad).map(_.name)

    (0 to kMax).foreach { k =>
      if(printProgress) println(s"Step #$k")

      // assume all constraints hold in this step
      constraints.foreach(c => solver.assert(enc.getConstraint(c)))

      // make sure the constraints are not contradictory
      if(options.checkConstraints) {
        val res = solver.check(produceModel = false)
        assert(res.isSat, s"Found unsatisfiable constraints in cycle $k")
      }

      if(options.checkBadStatesIndividually) {
        // check each bad state individually
        bads.zipWithIndex.foreach { case (b, bi) =>
          if(printProgress) print(s"- b$bi? ")

          solver.push()
          solver.assert(enc.getBadState(b))
          val res = solver.check(produceModel = false)

          // did we find an assignment for which the bad state is true?
          if(res.isSat) {
            if(printProgress) println("❌")
            val w = getWitness(sys, enc, k, Seq(bi))
            solver.pop()
            solver.pop()
            assert(solver.stackDepth == 0, s"Expected solver stack to be empty, not: ${solver.stackDepth}")
            return ModelCheckFail(w)
          } else {
            if(printProgress) println("✅")
          }
          solver.pop()
        }
      } else {
        val anyBad = smt.BVOr(bads.map(enc.getBadState))
        solver.push()
        solver.assert(anyBad)
        val res = solver.check(produceModel = false)

        // did we find an assignment for which at least one bad state is true?
        if(res.isSat) {
          val w = getWitness(sys, enc, k, bads.indices.toSeq)
          solver.pop()
          solver.pop()
          assert(solver.stackDepth == 0, s"Expected solver stack to be empty, not: ${solver.stackDepth}")
          return ModelCheckFail(w)
        }
        solver.pop()
      }

      // advance
      enc.unroll(solver)
    }

    // clean up
    solver.pop()
    assert(solver.stackDepth == 0, s"Expected solver stack to be empty, not: ${solver.stackDepth}")
    ModelCheckSuccess()
  }

  private def getWitness(sys: TransitionSystem, enc: SMTEncoding, kMax: Int, failedBad: Seq[Int]): Witness = {
    // btor2 numbers states in the order that they are declared in starting at zero
    val stateInit = sys.states.zipWithIndex.map {
      case (State(sym: smt.BVSymbol, _, _), ii) =>
        solver.getValue(enc.getSignalAt(sym, 0)) match {
          case Some(value) => (Some(ii -> value), None)
          case None => (None, None)
        }
      case (State(sym: smt.ArraySymbol, _, _), ii) =>
        val value = solver.getValue(enc.getSignalAt(sym, 0))
        (None, Some(ii -> value))
    }

    val regInit = stateInit.flatMap(_._1).toMap
    val memInit = stateInit.flatMap(_._2).toMap

    val inputs = (0 to kMax).map { k =>
      sys.inputs.zipWithIndex.flatMap { case (input, i) =>
        solver.getValue(enc.getSignalAt(input, k)).map(value => i -> value)
      }.toMap
    }

    Witness(failedBad, regInit, memInit, inputs)
  }

}

trait SMTEncoding {
  /** generate the system description */
  def defineHeader(solver: smt.Solver): Unit
  /** define the init state */
  def init(solver: smt.Solver): Unit
  /** add one more state */
  def unroll(solver: smt.Solver): Unit
  /** returns an expression representing the constraint in the current state */
  def getConstraint(name: String): smt.BVExpr
  /** returns an expression representing the constraint in the current state */
  def getBadState(name: String): smt.BVExpr
  /** returns an expression representing the signal in state k */
  def getSignalAt(sym: smt.BVSymbol, k: Int): smt.BVExpr
  def getSignalAt(sym: smt.ArraySymbol, k: Int): smt.ArrayExpr
}


class CompactEncoding(sys: TransitionSystem) extends SMTEncoding {
  import SMTTransitionSystemEncoder._
  private val stateType = id(sys.name + "_s")
  private val stateInitFun = id(sys.name + "_i")
  private val stateTransitionFun = id(sys.name + "_t")

  private val states = mutable.ArrayBuffer[smt.UTSymbol]()

  override def defineHeader(solver: smt.Solver): Unit = encode(sys, solver)

  private def appendState(solver: smt.Solver): smt.UTSymbol = {
    val s = smt.UTSymbol(s"s${states.length}", stateType)
    solver.runCommand(DeclareUninterpretedSymbol(s.name, s.tpe))
    states.append(s)
    s
  }

  def init(solver: smt.Solver): Unit = {
    assert(states.isEmpty)
    val s0 = appendState(solver)
    solver.assert(smt.BVFunctionCall(stateInitFun, List(s0), 1))
  }

  def unroll(solver: smt.Solver): Unit = {
    assert(states.nonEmpty)
    appendState(solver)
    val tStates = states.takeRight(2).toList
    solver.assert(smt.BVFunctionCall(stateTransitionFun, tStates, 1))
  }

  /** returns an expression representing the constraint in the current state */
  def getConstraint(name: String): smt.BVExpr = {
    assert(states.nonEmpty)
    val foo = id(name + "_f")
    smt.BVFunctionCall(foo, List(states.last), 1)
  }

  /** returns an expression representing the constraint in the current state */
  def getBadState(name: String): smt.BVExpr = {
    assert(states.nonEmpty)
    val foo = id(name + "_f")
    smt.BVFunctionCall(foo, List(states.last), 1)
  }

  def getSignalAt(sym: smt.BVSymbol, k: Int): smt.BVExpr = {
    assert(states.length > k, s"no state s$k")
    val state = states(k)
    val foo = id(sym.name + "_f")
    smt.BVFunctionCall(foo, List(state), sym.width)
  }

  def getSignalAt(sym: smt.ArraySymbol, k: Int): smt.ArrayExpr = {
    assert(states.length > k, s"no state s$k")
    val state = states(k)
    val foo = id(sym.name + "_f")
    smt.ArrayFunctionCall(foo, List(state), sym.indexWidth, sym.dataWidth)
  }
}

/** This Transition System encoding is directly inspired by yosys' SMT backend:
 * https://github.com/YosysHQ/yosys/blob/master/backends/smt2/smt2.cc
 * It if fairly compact, but unfortunately, the use of an uninterpreted sort for the state
 * prevents this encoding from working with boolector.
 * For simplicity reasons, we do not support hierarchical designs (no `_h` function).
 */
object SMTTransitionSystemEncoder {

  def encode(sys: TransitionSystem, solver: smt.Solver): Unit = {
    encode(sys).foreach(solver.runCommand)
  }

  def encode(sys: TransitionSystem): Iterable[SMTCommand] = {
    val cmds = mutable.ArrayBuffer[SMTCommand]()
    val name = sys.name

    // we currently do not support comments associated with signals
    val comments: Map[String, String] = Map()

    // declare state type
    val stateType = id(name + "_s")
    cmds += DeclareUninterpretedSort(stateType)

    // state symbol
    val State = smt.UTSymbol("state", stateType)
    val StateNext = smt.UTSymbol("state_n", stateType)

    // inputs and states are modelled as constants
    def declare(sym: smt.SMTSymbol, kind: String): Unit = {
      cmds ++= toDescription(sym, kind, comments.get)
      val s = smt.SMTSymbol.fromExpr(sym.name + SignalSuffix, sym)
      cmds += DeclareFunction(s, List(State))
    }
    sys.inputs.foreach(i => declare(i, "input"))
    sys.states.foreach(s => declare(s.sym, "register"))

    // signals are just functions of other signals, inputs and state
    def define(sym: smt.SMTSymbol, e: smt.SMTExpr, suffix: String = SignalSuffix): Unit = {
      cmds += DefineFunction(sym.name + suffix, List(State), replaceSymbols(SignalSuffix, State)(e))
    }
    sys.signals.foreach { signal =>
      val sym = signal.sym
      cmds ++= toDescription(sym, lblToKind(signal.lbl), comments.get)
      define(sym, signal.e)
    }

    // define the next and init functions for all states
    sys.states.foreach { state =>
      assert(state.next.nonEmpty, "Next function required")
      define(state.sym, state.next.get, NextSuffix)
      // init is optional
      state.init.foreach { init =>
        define(state.sym, init, InitSuffix)
      }
    }

    def defineConjunction(e: Iterable[smt.BVExpr], suffix: String): Unit = {
      define(smt.BVSymbol(name, 1), if(e.isEmpty) smt.True() else smt.BVAnd(e), suffix)
    }

    // the transition relation asserts that the value of the next state is the next value from the previous state
    // e.g., (reg state_n) == (reg_next state)
    val transitionRelations = sys.states.map { state =>
      val newState = replaceSymbols(SignalSuffix, StateNext)(state.sym)
      val nextOldState = replaceSymbols(NextSuffix, State)(state.sym)
      smt.SMTEqual(newState, nextOldState)
    }
    // the transition relation is over two states
    val transitionExpr = replaceSymbols(SignalSuffix, State)(smt.BVAnd(transitionRelations))
    cmds += DefineFunction(name + "_t", List(State, StateNext), transitionExpr)

    // The init relation just asserts that all init function hold
    val initRelations = sys.states.filter(_.init.isDefined).map { state =>
      val stateSignal = replaceSymbols(SignalSuffix, State)(state.sym)
      val initSignal = replaceSymbols(InitSuffix, State)(state.sym)
      smt.SMTEqual(stateSignal, initSignal)
    }
    defineConjunction(initRelations, "_i")

    // assertions and assumptions
    val bads = sys.signals.filter(_.lbl == IsBad).map(a => replaceSymbols(SignalSuffix, State)(a.sym))
    defineConjunction(bads.map(_.asInstanceOf[smt.BVExpr]), BadSuffix)
    val assumptions = sys.signals.filter(_.lbl == IsConstraint).map(a => replaceSymbols(SignalSuffix, State)(a.sym))
    defineConjunction(assumptions.map(_.asInstanceOf[smt.BVExpr]), AssumptionSuffix)

    cmds
  }

  def id(s: String): String = smt.SMTLibSerializer.escapeIdentifier(s)
  private val SignalSuffix = "_f"
  private val NextSuffix = "_next"
  private val InitSuffix = "_init"
  val BadSuffix = "_b"
  val AssumptionSuffix = "_u"
  private def lblToKind(lbl: SignalLabel): String = lbl match {
    case IsNode | IsInit | IsNext => "wire"
    case IsOutput => "output"
    // different from how the normal SMT encoding works, we actually defined bad states instead of safe states
    case IsBad => "bad"
    case IsConstraint => "assume"
    case IsFair => "fair"
  }
  private def toDescription(sym: smt.SMTSymbol, kind: String, comments: String => Option[String]): List[Comment] = {
    List(sym match {
      case smt.BVSymbol(name, width) => Comment(s"firrtl-smt2-$kind $name $width")
      case smt.ArraySymbol(name, indexWidth, dataWidth) => smt.Comment(s"firrtl-smt2-$kind $name $indexWidth $dataWidth")
    }) ++ comments(sym.name).map(smt.Comment)
  }

  // All signals are modelled with functions that need to be called with the state as argument,
  // this replaces all Symbols with function applications to the state.
  private def replaceSymbols(suffix: String, arg: smt.SMTFunctionArg, vars: Set[String] = Set())(e: smt.SMTExpr): smt.SMTExpr = e match {
    case smt.BVSymbol(name, width) if !vars(name) => smt.BVFunctionCall(id(name + suffix), List(arg), width)
    case smt.ArraySymbol(name, indexWidth, dataWidth) if !vars(name) => smt.ArrayFunctionCall(id(name + suffix), List(arg), indexWidth, dataWidth)
    case fa@ smt.BVForall(variable, _) => fa.mapExpr(replaceSymbols(suffix, arg, vars + variable.name))
    case other => other.mapExpr(replaceSymbols(suffix, arg, vars))
  }

  def determineLogic(features: TransitionSystemFeatures): smt.Logic = {
    val base = smt.SMTFeature.BitVector + smt.SMTFeature.UninterpretedFunctions
    val withArrays = if(features.hasArrays) base + smt.SMTFeature.Array else base
    val withQuantifiers = if(features.hasQuantifiers) withArrays else withArrays + smt.SMTFeature.QuantifierFree
    withQuantifiers
  }
}
