// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.mc

import maltese.smt
import maltese.smt.solvers
import maltese.smt.solvers.{Comment, DeclareFunction, DeclareUninterpretedSort, DefineFunction, SMTCommand, SetLogic}

import scala.collection.mutable

case class SMTModelCheckerOptions(checkConstraints: Boolean, checkBadStatesIndividually: Boolean, simplify: Boolean)
object SMTModelCheckerOptions {
  val Default: SMTModelCheckerOptions = SMTModelCheckerOptions(true, true, false)
  val Performance: SMTModelCheckerOptions = SMTModelCheckerOptions(false, false, true)
}

/** SMT based bounded model checking as an alternative to dispatching to a btor2 based external solver */
class SMTModelChecker(val solver: smt.Solver, options: SMTModelCheckerOptions = SMTModelCheckerOptions.Default) extends IsModelChecker {
  override val name: String = "SMTModelChecker with " + solver.name
  override val supportsUF: Boolean = true
  override val supportsQuantifiers: Boolean = solver.supportsQuantifiers

  override def check(sys: TransitionSystem, kMax: Int, fileName: Option[String] = None): ModelCheckResult = {
    require(kMax > 0 && kMax <= 2000, s"unreasonable kMax=$kMax")
    if(fileName.nonEmpty) println("WARN: dumping to file is not supported at the moment.")

    // create new context
    solver.push()

    // declare/define functions and encode the transition system
    val enc: SMTEncoding = ??? // new CompactEncoding(sys, options.simplify)
    enc.defineHeader(solver)
    enc.init(solver)

    val constraints = sys.signals.filter(_.lbl == IsConstraint).map(_.name)
    val bads = sys.signals.filter(_.lbl == IsBad).map(_.name)

    (0 to kMax).foreach { k =>
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
          solver.push()
          solver.assert(enc.getBadState(b))
          val res = solver.check(produceModel = false)

          // did we find an assignment for which the bad state is true?
          if(res.isSat) {
            val w = getWitness(sys, enc, k, Seq(bi))
            solver.pop()
            return ModelCheckFail(w)
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
          return ModelCheckFail(w)
        }
        solver.pop()
      }

      // advance
      enc.unroll(solver)
    }

    // clean up
    solver.pop()
    ModelCheckSuccess()
  }

  private def getWitness(sys: TransitionSystem, enc: SMTEncoding, kMax: Int, failedBad: Seq[Int]): Witness = {
    val regInit = sys.states.zipWithIndex.map { case (state, i) =>
      assert(!state.sym.isInstanceOf[smt.ArraySymbol], "TODO: support arrays!")
      val value = solver.getValue(enc.getSignalAt(state.sym.asInstanceOf[smt.BVSymbol], 0)).get
      i -> value
    }.toMap

    val inputs = (0 to kMax).map { k =>
      sys.inputs.zipWithIndex.map { case (input, i) =>
        val value = solver.getValue(enc.getSignalAt(input, k)).get
        i -> value
      }.toMap
    }

    Witness(failedBad, regInit, Map(), inputs)
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

    // set appropriate logic
    cmds += SetLogic(determineLogic(sys))

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
    cmds += solvers.DefineFunction(name + "_t", List(State, StateNext), transitionExpr)

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

  private def id(s: String): String = smt.SMTLibSerializer.escapeIdentifier(s)
  private val SignalSuffix = "_f"
  private val NextSuffix = "_next"
  private val InitSuffix = "_init"
  private val BadSuffix = "_b"
  private val AssumptionSuffix = "_u"
  private def lblToKind(lbl: SignalLabel): String = lbl match {
    case IsNode => "wire"
    case IsOutput => "output"
    // different from how the normal SMT encoding works, we actually defined bad states instead of safe states
    case IsBad => "bad"
    case IsConstraint => "assume"
  }
  private def toDescription(sym: smt.SMTSymbol, kind: String, comments: String => Option[String]): List[Comment] = {
    List(sym match {
      case smt.BVSymbol(name, width) => solvers.Comment(s"firrtl-smt2-$kind $name $width")
      case smt.ArraySymbol(name, indexWidth, dataWidth) => solvers.Comment(s"firrtl-smt2-$kind $name $indexWidth $dataWidth")
    }) ++ comments(sym.name).map(solvers.Comment)
  }

  // All signals are modelled with functions that need to be called with the state as argument,
  // this replaces all Symbols with function applications to the state.
  private def replaceSymbols(suffix: String, arg: smt.SMTFunctionArg)(e: smt.SMTExpr): smt.SMTExpr = e match {
    case smt.BVSymbol(name, width) => smt.BVFunctionCall(id(name + suffix), List(arg), width)
    case smt.ArraySymbol(name, indexWidth, dataWidth) => smt.ArrayFunctionCall(id(name + suffix), List(arg), indexWidth, dataWidth)
    case other => other.mapExpr(replaceSymbols(suffix, arg))
  }

  private def determineLogic(sys: TransitionSystem): smt.Logic = {
    val features = TransitionSystem.analyzeFeatures(sys)
    val base = smt.SMTFeature.BitVector + smt.SMTFeature.UninterpretedFunctions
    val withArrays = if(features.hasArrays) base + smt.SMTFeature.Array else base
    val withQuantifiers = if(features.hasQuantifiers) withArrays else withArrays + smt.SMTFeature.QuantifierFree
    withQuantifiers
  }
}

/**
 * This Transition System encoding is directly inspired by yosys' SMT backend:
 * https://github.com/YosysHQ/yosys/blob/master/backends/smt2/smt2.cc
 * */
class CompactEncoding(sys: TransitionSystem, doSimplify: Boolean = false) extends SMTEncoding {
  val simplify: smt.SMTExpr => smt.SMTExpr = if(doSimplify) { smt.SMTSimplifier.simplify } else { e => e }
  private val name = sys.name
  private val stateType = smt.UninterpretedType(name + "_s")
  private val stateInitFun = smt.Symbol(name + "_is", smt.MapType(List(stateType), smt.BoolType))
  private val stateTransitionFun = smt.Symbol(name + "_t", smt.MapType(List(stateType, stateType), smt.BoolType))
  private val constraintFuns = sys.constraints.zipWithIndex.map{ case(c,ii) =>
    c -> smt.Symbol(s"c$ii", smt.MapType(List(stateType), smt.BoolType))
  }.toMap
  private val badFuns = sys.bad.zipWithIndex.map{ case(b,ii) =>
    b -> smt.Symbol(s"b$ii", smt.MapType(List(stateType), smt.BoolType))
  }.toMap
  private val states = mutable.ArrayBuffer[smt.Symbol]()


  def defineHeader(solver: smt.Solver): Unit = {
    def define(f: smt.DefineFun): Unit = solver.define(f.copy(e = simplify(f.e)))
    solver.declare(stateType)

    val stateSymbol = smt.Symbol("state", stateType)
    val nextStateSymbol = smt.Symbol("next_state", stateType)

    // input, output and state functions
    val outputSignals = sys.outputs.map(o => smt.Symbol(o._1, o._2.typ))
    val signals = sys.states.map(_.sym) ++ sys.inputs ++ outputSignals
    val signalFuns = signals.map(s => s -> smt.Symbol(s.id + "_f", smt.MapType(List(stateType), s.typ))).toMap
    val signalSubs = signalFuns.mapValues(f => smt.FunctionApplication(f, List(stateSymbol)))

    // we want to leave state and inputs uninterpreted
    (sys.states.map(_.sym) ++ sys.inputs).foreach(s => solver.declare(signalFuns(s)))

    // outputs can be defined in terms of state and inputs (and maybe other outputs ???)
    sys.outputs.foreach { case (name, expr) =>
      val funExpr = substituteSmtSymbols(expr, signalSubs)
      val funSym = signalFuns(smt.Symbol(name, expr.typ))
      val fun = smt.DefineFun(funSym, List(stateSymbol), funExpr)
      define(fun)
    }

    // define state next and init functions
    val transitionRelations = sys.states.map { s =>
      assert(s.next.nonEmpty, "Next function required")
      val funExpr = substituteSmtSymbols(s.next.get, signalSubs)
      val funSym = smt.Symbol(s.sym.id + "_next", smt.MapType(List(stateType), funExpr.typ))
      val fun = smt.DefineFun(funSym, List(stateSymbol), funExpr)
      define(fun)

      // on a transition, the next state is equal to the result of the next state function applied to the old state
      val newState = smt.FunctionApplication(signalFuns(s.sym), List(nextStateSymbol))
      val nextOldState = smt.FunctionApplication(funSym, List(stateSymbol))
      eq(newState, nextOldState)
    }

    val initRelations = sys.states.collect { case s @ smt.State(_, Some(init), _) =>
      val funExpr = substituteSmtSymbols(init, signalSubs)
      val funSym = smt.Symbol(s.sym.id + "_init", smt.MapType(List(stateType), funExpr.typ))
      val fun = smt.DefineFun(funSym, List(stateSymbol), funExpr)
      define(fun)

      // on init, the current state is equal to the init state
      eq(signalSubs(s.sym), smt.FunctionApplication(funSym, List(stateSymbol)))
    }

    // define init function
    define(smt.DefineFun(stateInitFun, List(stateSymbol), conjunction(initRelations)))

    // define transition function
    define(smt.DefineFun(stateTransitionFun, List(stateSymbol, nextStateSymbol), conjunction(transitionRelations)))

    // define constraint functions
    constraintFuns.foreach { case (expr, funSym) =>
      val funExpr = substituteSmtSymbols(expr, signalSubs)
      val fun = smt.DefineFun(funSym, List(stateSymbol), funExpr)
      define(fun)
    }

    // define bad state functions
    badFuns.foreach { case (expr, funSym) =>
      val funExpr = substituteSmtSymbols(expr, signalSubs)
      val fun = smt.DefineFun(funSym, List(stateSymbol), funExpr)
      define(fun)
    }
  }

  private def appendState(): smt.Symbol = {
    val s = smt.Symbol(s"s${states.length}", stateType)
    states.append(s)
    s
  }

  def init(solver: smt.Solver): Unit = {
    assert(states.isEmpty)
    val s0 = appendState()
    solver.assert(smt.FunctionApplication(stateInitFun, List(s0)))
  }

  def unroll(solver: smt.Solver): Unit = {
    assert(states.nonEmpty)
    appendState()
    val tStates = states.takeRight(2).toList
    solver.assert(smt.FunctionApplication(stateTransitionFun, tStates))
  }

  /** returns an expression representing the constraint in the current state */
  def getConstraint(name: String): smt.BVExpr = {
    assert(states.nonEmpty)
    val foo = constraintFuns(e)
    smt.FunctionApplication(foo, List(states.last))
  }

  /** returns an expression representing the constraint in the current state */
  def getBadState(name: String): smt.BVExpr = {
    assert(states.nonEmpty)
    val foo = badFuns(e)
    smt.FunctionApplication(foo, List(states.last))
  }

  def getSignalAt(sym: smt.BVSymbol, k: Int): smt.BVExpr = {
    assert(states.length > k, s"no state s$k")
    val state = states(k)
    val foo = smt.Symbol(signal.id + "_f", smt.MapType(List(stateType), signal.typ))
    smt.FunctionApplication(foo, List(state))
  }

}