// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

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

    val solver = Yices2()
    val automaton = makePasoAutomaton(problem.spec.untimed, problem.spec.protocols, solver)
    println(automaton.serialize)

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
}
