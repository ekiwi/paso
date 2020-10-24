// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import Chisel.log2Ceil
import maltese.mc.{IsBad, Signal, State, TransitionSystem}
import maltese.{mc, smt}
import maltese.smt.solvers.{Solver, Yices2}
import paso.protocols.{PasoAutomatonEncoder, ProtocolGraph}
import paso.untimed

trait Assertion { def toExpr: smt.BVExpr }
case class BasicAssertion(guard: smt.BVExpr, pred: smt.BVExpr) extends Assertion {
  override def toExpr: smt.BVExpr = smt.BVImplies(guard, pred)
}
case class ForAllAssertion(variable: smt.BVSymbol, start: Int, end: Int, guard: smt.BVExpr, pred: smt.BVExpr) extends Assertion {
  override def toExpr: smt.BVExpr = {
    val max = 1 << variable.width
    val isFullRange = start == 0 && end == max
    val g = if(isFullRange) { guard } else {
      val lower = smt.BVComparison(smt.Compare.GreaterEqual, variable, smt.BVLiteral(start, variable.width), signed=false)
      val upper = smt.BVNot(smt.BVComparison(smt.Compare.Greater, variable, smt.BVLiteral(end-1, variable.width), signed=false))
      smt.BVAnd(guard, smt.BVAnd(lower, upper))
    }
    smt.BVForall(variable, smt.BVImplies(g, pred))
  }
}

case class UntimedModel(sys: mc.TransitionSystem, methods: Seq[untimed.MethodInfo]) {
  def name: String = sys.name
  def addPrefix(prefix: String): UntimedModel = copy(sys = sys.copy(name = prefix + name))
}
case class Spec(untimed: UntimedModel, protocols: Seq[ProtocolGraph])
case class Subspec(instance: String, ioSymbols: Seq[smt.BVSymbol], spec: Spec, binding: Option[String])
case class VerificationProblem(impl: TransitionSystem, spec: Spec, subspecs: Seq[Subspec],
                               invariances: Seq[Assertion], mapping: Seq[Assertion])

object VerificationProblem {
  def verify(problem: VerificationProblem, opt: paso.ProofOptions): Unit = {
    // check to see if the mappings contain quantifiers
    val quantifierFree = !(problem.mapping ++ problem.invariances).exists(_.isInstanceOf[ForAllAssertion])
    assert(quantifierFree, "TODO: expand quantifiers when needed (for btor2 and yices)")
    val checker =  new mc.BtormcModelChecker()

    // turn the protocol and untimed model into a paso automaton
    val solver = Yices2()
    val spec = makePasoAutomaton(problem.spec.untimed, problem.spec.protocols, solver)

    // connect the implementation to the global reset
    val impl = connectToReset(problem.impl)

    // encode invariants
    val startState = smt.BVSymbol(spec.name + ".automaton.startState", 1)
    val invariants = encodeInvariants(startState, problem.invariances ++ problem.mapping)

    // for the base case we combine everything together with a reset
    val baseCase = List(generateInitialReset(), impl, spec, invariants)
    val baseCaseSys = mc.TransitionSystem.combine("BaseCase", baseCase)

    // generate base case btor
    println(baseCaseSys.serialize)
    checker.check(baseCaseSys, kMax = 1, fileName = Some("basecase.btor2"))

    // check all our simplifications
    assert(!opt.checkSimplifications, "Cannot check simplifications! (not implement)")
  }

  def bmc(problem: VerificationProblem, solver: paso.SolverName, kMax: Int): Unit = {
    assert(problem.mapping.isEmpty)
    assert(problem.invariances.isEmpty)

    throw new NotImplementedError("TODO: implement BMC")
  }

  private def makePasoAutomaton(untimed: UntimedModel, protocols: Iterable[ProtocolGraph], solver: Solver): TransitionSystem = {
    val automaton = new PasoAutomatonEncoder(untimed, protocols, solver).run()
    new PasoAutomatonToTransitionSystem(automaton).run()
  }

  private def generateInitialReset(length: Int = 1): TransitionSystem = {
    assert(length >= 1)
    val counterBits = List(log2Ceil(length), 1).max
    val counterMax = smt.BVLiteral((BigInt(1) << counterBits) - 1, counterBits)
    val counter = smt.BVSymbol("resetCounter", counterBits)
    val counterNext = smt.BVIte(smt.BVEqual(counter, counterMax), counter, smt.BVOp(smt.Op.Add, counter, smt.BVLiteral(1, counterBits)))
    val state = State(counter, init=Some(smt.BVLiteral(0, counterBits)), next=Some(counterNext))
    val reset = Signal("reset", smt.BVComparison(smt.Compare.GreaterEqual, counter, smt.BVLiteral(length, counterBits), signed = false))
    mc.TransitionSystem("reset", List(), List(state), List(reset))
  }

  private def generateDisabledReset(): TransitionSystem = {
    val reset = mc.Signal("reset", smt.BVLiteral(0, 1))
    mc.TransitionSystem("reset", List(), List(), List(reset))
  }

  private def connectToReset(sys: TransitionSystem): TransitionSystem = {
    val resetName = sys.name + ".reset"
    assert(sys.inputs.exists(_.name == resetName), s"Failed to find the reset port of ${sys.name}")
    val connectReset = mc.Signal(resetName, smt.BVSymbol("reset", 1))
    // filter out reset input
    val inputs = sys.inputs.filterNot(_.name == resetName)
    val signals = connectReset +: sys.signals
    sys.copy(inputs=inputs, signals=signals)
  }

  private def encodeInvariants(start: smt.BVExpr, invariants: Iterable[Assertion]): TransitionSystem = {
    val guard = smt.BVSymbol("inv", 1)
    val connectGuard = mc.Signal(guard.name, smt.BVAnd(smt.BVNot(smt.BVSymbol("reset", 1)), start))
    val exprs = invariants.map {
      case BasicAssertion(smt.True(), pred) => smt.BVImplies(guard, pred)
      case BasicAssertion(local, pred) => smt.BVImplies(smt.BVAnd(guard, local), pred)
      case f : ForAllAssertion => smt.BVImplies(guard, f.toExpr)
    }
    // TODO: better names + debug info
    val bads = exprs.zipWithIndex.map { case (e, i) => mc.Signal(s"inv_$i", smt.BVNot(e), IsBad)}.toList
    mc.TransitionSystem("Invariants", List(), List(), connectGuard +: bads)
  }
}
