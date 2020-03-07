// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

// contains data structures used for verification
// mostly language neutral (aka Chisel independent)

package paso.verification

import paso.chisel.SmtHelpers
import uclid.smt

// things that need to be verified:
// (1) do assertions on untimed model always hold? (can we do an inductive proof?)
// (2) do the invariances over the implementation hold after a reset?
// (3) check the base case for the mapping function (see MC 11.1 and Definition 13.2):
//     3.1) for all initial states in the untimed model, there exists a state in the
//          timed model and that state is pan initial state
//     TODO
// (4)

// Verification Graph
trait VerificationEdge { val methods: Set[String] ; val next: VerificationNode }
trait VerificationNode { val next: Seq[VerificationEdge] }
case class PendingInputNode(next: Seq[InputEdge] = Seq()) extends VerificationNode
case class PendingOutputNode(next: Seq[OutputEdge] = Seq()) extends VerificationNode
case class InputEdge(constraints: Seq[smt.Expr] = Seq(), mappings: Seq[smt.Expr] = Seq(), methods: Set[String], next: PendingOutputNode) extends VerificationEdge
case class OutputEdge(constraints: Seq[smt.Expr] = Seq(), mappings: Seq[smt.Expr] = Seq(), methods: Set[String], next: PendingInputNode) extends VerificationEdge

case class Assertion(guard: smt.Expr, pred: smt.Expr)

case class VerificationProblem(
  impl: smt.SymbolicTransitionSystem,
  untimed: UntimedModel,
  protocols: Map[String, PendingInputNode],
  invariances: Seq[Assertion],
  mapping: Seq[Assertion]
)

object VerificationProblem {
  def verify(p: VerificationProblem): Unit = {
    val tasks = Seq(new VerifyMapping)
    tasks.foreach(_.run(p))
  }
}

class VerifyMapping extends VerificationTask with SmtHelpers with HasSolver {
  override val solverName: String = "z3"
  val solver = new smt.SMTLIB2Interface(List("z3", "-in"))
  override protected def execute(p: VerificationProblem): Unit = {
    val impl_states = p.impl.states.map(_.sym)
    val impl_init_const = conjunction(p.impl.states.collect { case smt.State(sym, Some(init), _) => eq(sym, init) })
    val spec_states = p.untimed.state.map{ case (name, tpe) => smt.Symbol(name, tpe) }.toSeq
    val spec_init_const = conjunction(p.untimed.init.map{ case (name, value) => eq(smt.Symbol(name, p.untimed.state(name)), value) }.toSeq)
    val mapping_const = conjunction(p.mapping.map{ a => implies(a.guard, a.pred) })

    // forall initial states of the implementation there exists an initial state in the specification for which the mapping holds
    val unmappable_impl = and(impl_init_const, forall(spec_states, not(and(spec_init_const, mapping_const))))

    val impl_res = check(unmappable_impl)
    assert(impl_res.isFalse, s"Found an implementation initial state for which there is no mapping: $impl_res")

    // forall initial states of the specification there exists an initial state in the implementation for which the mapping holds
    val unmappable_spec = and(spec_init_const, forall(impl_states, not(and(impl_init_const, mapping_const))))

    val spec_res = check(unmappable_spec)
    assert(spec_res.isFalse, s"Found a specification initial state for which there is no mapping: $spec_res")
  }
}


abstract class VerificationTask {
  val solverName: String
  protected def execute(p: VerificationProblem): Unit
  def run(p: VerificationProblem): Unit = execute(p)
}
