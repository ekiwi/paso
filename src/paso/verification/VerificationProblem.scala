// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import Chisel.log2Ceil
import maltese.smt
import maltese.smt.solvers.{Solver, Yices2}
import paso.protocols.{PasoAutomatonEncoder, ProtocolGraph}

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

case class Spec(untimed: UntimedModel, protocols: Seq[ProtocolGraph])
case class Subspec(instance: String, ioSymbols: Seq[smt.BVSymbol], spec: Spec, binding: Option[String])
case class VerificationProblem(impl: smt.TransitionSystem, spec: Spec, subspecs: Seq[Subspec],
                               invariances: Seq[Assertion], mapping: Seq[Assertion])

object VerificationProblem {
  def verify(problem: VerificationProblem, opt: paso.ProofOptions): Unit = {
    // check to see if the mappings contain quantifiers
    val quantifierFree = !(problem.mapping ++ problem.invariances).exists(_.isInstanceOf[ForAllAssertion])

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
    val baseCaseSys = combineSystems("BaseCase", baseCase)
    println(baseCaseSys.serialize)

    // check all our simplifications
    assert(!opt.checkSimplifications, "Cannot check simplifications! (not implement)")
  }

  def bmc(problem: VerificationProblem, solver: paso.SolverName, kMax: Int): Unit = {
    assert(problem.mapping.isEmpty)
    assert(problem.invariances.isEmpty)

    throw new NotImplementedError("TODO: implement BMC")
  }

  private def makePasoAutomaton(untimed: UntimedModel, protocols: Iterable[ProtocolGraph], solver: Solver): smt.TransitionSystem = {
    val automaton = new PasoAutomatonEncoder(untimed, protocols, solver).run()
    new PasoAutomatonToTransitionSystem(automaton).run()
  }

  private def generateInitialReset(length: Int = 1): smt.TransitionSystem = {
    assert(length >= 1)
    val counterBits = List(log2Ceil(length), 1).max
    val counterMax = smt.BVLiteral((BigInt(1) << counterBits) - 1, counterBits)
    val counter = smt.BVSymbol("resetCounter", counterBits)
    val counterNext = smt.BVIte(smt.BVEqual(counter, counterMax), counter, smt.BVOp(smt.Op.Add, counter, smt.BVLiteral(1, counterBits)))
    val state = smt.State(counter, init=Some(smt.BVLiteral(0, counterBits)), next=Some(counterNext))
    val reset = smt.Signal("reset", smt.BVComparison(smt.Compare.GreaterEqual, counter, smt.BVLiteral(length, counterBits), signed = false))
    smt.TransitionSystem("reset", List(), List(state), List(reset))
  }

  private def generateDisabledReset(): smt.TransitionSystem = {
    val reset = smt.Signal("reset", smt.BVLiteral(0, 1))
    smt.TransitionSystem("reset", List(), List(), List(reset))
  }

  private def connectToReset(sys: smt.TransitionSystem): smt.TransitionSystem = {
    val resetName = sys.name + ".reset"
    assert(sys.inputs.exists(_.name == resetName), s"Failed to find the reset port of ${sys.name}")
    val connectReset = smt.Signal(resetName, smt.BVSymbol("reset", 1))
    // filter out reset input
    val inputs = sys.inputs.filterNot(_.name == resetName)
    val signals = connectReset +: sys.signals
    sys.copy(inputs=inputs, signals=signals)
  }

  private def encodeInvariants(start: smt.BVExpr, invariants: Iterable[Assertion]): smt.TransitionSystem = {
    val guard = smt.BVSymbol("inv", 1)
    val connectGuard = smt.Signal(guard.name, smt.BVAnd(smt.BVNot(smt.BVSymbol("reset", 1)), start))
    val exprs = invariants.map {
      case BasicAssertion(smt.True(), pred) => smt.BVImplies(guard, pred)
      case BasicAssertion(local, pred) => smt.BVImplies(smt.BVAnd(guard, local), pred)
      case f : ForAllAssertion => smt.BVImplies(guard, f.toExpr)
    }
    // TODO: better names + debug info
    val bads = exprs.zipWithIndex.map { case (e, i) => smt.Signal(s"inv_$i", smt.BVNot(e), smt.IsBad)}.toList
    smt.TransitionSystem("Invariants", List(), List(), connectGuard +: bads)
  }

  private def combineSystems(name: String, sys: List[smt.TransitionSystem]): smt.TransitionSystem = {
    smt.TransitionSystem(name,
      inputs = sys.flatMap(_.inputs),
      states = sys.flatMap(_.states),
      signals = sys.flatMap(_.signals)
    )
  }
}
