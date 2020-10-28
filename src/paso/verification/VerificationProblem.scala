// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import Chisel.log2Ceil
import maltese.mc.{IsModelChecker, ModelCheckFail, ModelCheckSuccess, Signal, State, TransitionSystem, TransitionSystemSimulator}
import maltese.{mc, smt}
import maltese.smt.solvers.{Solver, Yices2}
import paso.protocols.{PasoAutomatonEncoder, ProtocolGraph}
import paso.untimed

case class UntimedModel(sys: mc.TransitionSystem, methods: Seq[untimed.MethodInfo]) {
  def name: String = sys.name
  def addPrefix(prefix: String): UntimedModel = copy(sys = sys.copy(name = prefix + name))
}
case class Spec(untimed: UntimedModel, protocols: Seq[ProtocolGraph])
case class Subspec(spec: Spec, binding: Option[String])
case class VerificationProblem(impl: TransitionSystem, spec: Spec, subspecs: Seq[Subspec], invariants: TransitionSystem)

object VerificationProblem {
  def verify(problem: VerificationProblem, opt: paso.ProofOptions): Unit = {
    val checker = makeChecker(opt.modelChecker)
    val solver = Yices2()

    // connect the implementation to the global reset
    val impl = connectToReset(problem.impl)

    // turn spec into a monitoring automaton
    val (spec, longestPath) = makePasoAutomaton(problem.spec.untimed, problem.spec.protocols, solver)

    // encode invariants (if any)
    val invariants = encodeInvariants(spec.name, problem.invariants)

    // for the base case we combine everything together with a reset
    val baseCaseSys = mc.TransitionSystem.combine("base",
      List(generateBmcConditions(1), impl, spec, invariants))
    val baseCaseSuccess = check(checker, baseCaseSys, kMax = 1)

    // for the induction we start the automaton in its initial state and assume
    val inductionStep = mc.TransitionSystem.combine("induction",
      List(generateInductionConditions(), impl, spec, invariants, startInStateZero(spec.name)))
    val inductionLength = longestPath
    val inductionSuccess = check(checker, inductionStep, kMax = inductionLength)

    // check results
    assert(baseCaseSuccess, s"Some of your invariants are not true after reset! Please consult ${baseCaseSys.name}.vcd")
    assert(inductionSuccess, s"Induction step failed! Please consult ${inductionStep.name}.vcd")

    // check all our simplifications
    assert(!opt.checkSimplifications, "Cannot check simplifications! (not implement)")
  }

  def bmc(problem: VerificationProblem, modelChecker: paso.SolverName, kMax: Int): Unit = {
    val resetLength = 1
    val checker = makeChecker(modelChecker)
    val solver = Yices2()

    // connect the implementation to the global reset
    val impl = connectToReset(problem.impl)

    // turn spec into a monitoring automaton
    val (spec, _) = makePasoAutomaton(problem.spec.untimed, problem.spec.protocols, solver)

    // encode invariants (if any)
    val invariants = encodeInvariants(spec.name, problem.invariants)

    // we do a reset in the beginning
    val bmcSys = mc.TransitionSystem.combine("bmc",
      List(generateBmcConditions(resetLength), impl, spec, invariants))

    // call checker
    val success = check(checker, bmcSys, kMax + resetLength)
    assert(success, s"Found a disagreement between implementation and spec. Please consult ${bmcSys.name}.vcd")
  }

  private def makeChecker(name: paso.SolverName): IsModelChecker = {
    if(name == paso.Btormc) {
      new mc.BtormcModelChecker()
    } else {
      throw new NotImplementedError(s"TODO: $name")
    }
  }

  private def check(checker: IsModelChecker, sys: TransitionSystem, kMax: Int, printSys: Boolean = false, debug: Iterable[smt.BVSymbol] = List()): Boolean = {
    val btorFile = sys.name + ".btor2"
    val vcdFile = sys.name + ".vcd"

    val fullSys = if(debug.isEmpty) { sys } else { observe(sys, debug) }
    if(printSys) { println(fullSys.serialize) }
    val res = checker.check(fullSys, kMax = kMax, fileName = Some(btorFile))
    res match {
      case ModelCheckFail(witness) =>
        val sim = new TransitionSystemSimulator(fullSys)
        sim.run(witness, vcdFileName = Some(vcdFile))
        println(s"${fullSys.name} fails!")
        false
      case ModelCheckSuccess() =>
        // println(s"${fullSys.name} works!")
        true
    }
  }

  private def makePasoAutomaton(untimed: UntimedModel, protocols: Iterable[ProtocolGraph], solver: Solver): (TransitionSystem, Int) = {
    val automaton = new PasoAutomatonEncoder(untimed, protocols, solver).run()
    val sys = new PasoAutomatonToTransitionSystem(automaton).run()
    val longestPath = automaton.longestPath
    (sys, longestPath)
  }

  private def generateBmcConditions(resetLength: Int = 1): TransitionSystem = {
    val reset = generateInitialReset(resetLength)
    val invertAssert = mc.Signal("invertAssert", smt.False())
    reset.copy(name="BmcConditions", signals = reset.signals :+ invertAssert)
  }

  private def generateInitialReset(length: Int = 1): TransitionSystem = {
    assert(length >= 1)
    val counterBits = List(log2Ceil(length), 1).max
    val counterMax = smt.BVLiteral((BigInt(1) << counterBits) - 1, counterBits)
    val counter = smt.BVSymbol("resetCounter", counterBits)
    val counterNext = smt.BVIte(smt.BVEqual(counter, counterMax), counter, smt.BVOp(smt.Op.Add, counter, smt.BVLiteral(1, counterBits)))
    val state = State(counter, init=Some(smt.BVLiteral(0, counterBits)), next=Some(counterNext))
    val reset = Signal("notReset", smt.BVComparison(smt.Compare.GreaterEqual, counter, smt.BVLiteral(length, counterBits), signed = false))
    val notReset = Signal("reset", smt.BVNot(smt.BVSymbol("notReset", 1)))
    mc.TransitionSystem("reset", List(), List(state), List(reset, notReset))
  }

  private def generateInductionConditions(): TransitionSystem = {
    // during induction, the reset is disabled
    val reset = mc.Signal("reset", smt.BVLiteral(0, 1))
    val notReset = mc.Signal("notReset", smt.BVLiteral(1, 1))

    // the initial state is constrained with the invariants + the automaton state is 0
    val isInit = smt.BVSymbol("isInit", 1)
    val state = State(isInit, init = Some(smt.True()), next = Some(smt.False()))
    val invertAssert = mc.Signal("invertAssert", isInit)

    mc.TransitionSystem("InductionConditions", List(), List(state), List(reset, notReset, invertAssert))
  }

  private def startInStateZero(specName: String): TransitionSystem = {
    val isInit = smt.BVSymbol("isInit", 1)
    val startAtZero = Signal("startAtZero", smt.BVImplies(isInit, smt.BVSymbol(specName + ".automaton.stateIsZero", 1)), mc.IsConstraint)
    mc.TransitionSystem("StartInStateZero", List(), List(), List(startAtZero))
  }

  private def connectToReset(sys: TransitionSystem): TransitionSystem =
    TransitionSystem.connect(sys, Map(sys.name + ".reset" ->  reset))

  private def encodeInvariants(specName: String, invariants: TransitionSystem): TransitionSystem = {
    val startState = smt.BVSymbol(specName + ".automaton.startState", 1)
    val invertAssert = smt.BVSymbol("invertAssert", 1)
    val sys = TransitionSystem.connect(invariants, Map(
      invariants.name + ".reset" -> reset,
      invariants.name + ".enabled" -> smt.BVAnd(smt.BVNot(reset), startState),
      invariants.name + ".invertAssert" -> invertAssert,
    ))
    assert(sys.inputs.isEmpty, s"Unexpected inputs: ${sys.inputs.mkString(", ")}")
    sys
  }

  private def observe(sys: TransitionSystem, signals: Iterable[smt.BVSymbol]): TransitionSystem = {
    val oState = signals.map(s => mc.State(s.rename(s.name + "$o"), None, None))
    val constraints = signals.map(s => mc.Signal(s.name + "$eq", smt.BVEqual(s, s.rename(s.name + "$o")), mc.IsConstraint))
    sys.copy(states = sys.states ++ oState, signals = sys.signals ++ constraints)
  }

  private val reset = smt.BVSymbol("reset", 1)
}
