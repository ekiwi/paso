// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

// contains data structures used for verification
// mostly language neutral (aka Chisel independent)

package paso.verification

import paso.chisel.{SMTSimplifier, SmtHelpers}
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
    val tasks = Seq(new VerifyMapping, new VerifyBaseCase, new VerifyMethods(oneAtATime = true))
    tasks.foreach(_.run(p))
  }
}



class VerifyMethods(oneAtATime: Boolean) extends VerificationTask with SmtHelpers with HasSolver {
  override val solverName: String = "yices2"
  val solver = new smt.SMTLIB2Interface(List("yices-smt2"))

  override protected def execute(p: VerificationProblem): Unit = {
    // first we need to merge the protocol graph to ensure that methods are independent
    // - independence in this case means that for common inputs, the expected outputs are not mutually exclusive
    val combined = p.protocols.values.reduce(VerificationGraph.merge) // this will fail if methods are not independent


  }
}

class VerifyMapping extends VerificationTask with SmtHelpers with HasSolver {
  override val solverName: String = "z3"
  val solver = new smt.SMTLIB2Interface(List("z3", "-in"))

  override protected def execute(p: VerificationProblem): Unit = {
    val impl_states = p.impl.states.map(_.sym).prefix(p.impl.name.get + ".").toSeq
    val impl_init_const = conjunction(VerificationTask.getResetState(p.impl).map{
      case (smt.Symbol(name, tpe), value) => eq(smt.Symbol(p.impl.name.get + "." + name, tpe), value)
    }.toSeq)
    val spec_states = p.untimed.state.map{ case (name, tpe) => smt.Symbol(name, tpe) }.prefix(p.untimed.name + ".").toSeq
    val spec_init_const = conjunction(p.untimed.init.map{
      case (name, value) => eq(smt.Symbol(p.untimed.name + "." + name, p.untimed.state(name)), value)
    }.toSeq)
    val mapping_const = conjunction(p.mapping.map{ a => implies(a.guard, a.pred) })

    // TODO: ideas on how to get solver to verify mappings
    // 1.) try to merge array comparisons (if all locations are compared, just compare the whole array)
    // 2.) try to do static slicing in order to check independent state mappings independently
    // 3.) identify bitwise, bijective mappings that don't impose any constraints; if the initial value is also
    //     unconstrained -> no need to call the solver

    try {
      // forall initial states of the implementation there exists an initial state in the specification for which the mapping holds
      val unmappable_impl = SMTSimplifier.simplify(and(impl_init_const, forall(spec_states, not(and(spec_init_const, mapping_const)))))

      val impl_res = check(unmappable_impl)
      assert(impl_res.isFalse, s"Found an implementation initial state for which there is no mapping: $impl_res")

      // forall initial states of the specification there exists an initial state in the implementation for which the mapping holds
      val unmappable_spec = SMTSimplifier.simplify(and(spec_init_const, forall(impl_states, not(and(impl_init_const, mapping_const)))))

      val spec_res = check(unmappable_spec)
      assert(spec_res.isFalse, s"Found a specification initial state for which there is no mapping: $spec_res")
    } catch {
      case e: uclid.Utils.AssertionError =>
        assert(e.getMessage.contains("unknown"))
        println(s"WARNING: cannot prove mapping correct: $solverName returned unknown")
    }
  }
}

class VerifyBaseCase extends VerificationTask with SmtHelpers with HasSolver {
  override val solverName: String = "z3"
  val solver = new smt.SMTLIB2Interface(List("z3", "-in"))

  override protected def execute(p: VerificationProblem): Unit = {
    val impl_init_const = conjunction(VerificationTask.getResetState(p.impl).map{ case (sym, value) => eq(sym, value)}.toSeq)
    val inv_const = conjunction(p.invariances.map{ a => implies(a.guard, a.pred) })

    // make sure invariances hold after reset
    val hold = SMTSimplifier.simplify(implies(impl_init_const, inv_const))
    val res = check(not(hold))
    assert(res.isFalse, s"FAIL: Invariances are not necessarily true after reset: ${res.model}")
  }
}

abstract class VerificationTask {
  val solverName: String
  protected def execute(p: VerificationProblem): Unit
  def run(p: VerificationProblem): Unit = {
    val start = System.nanoTime()
    execute(p)
    val end = System.nanoTime()
    println(s"Executed ${this.getClass.getSimpleName} with $solverName in ${(end - start)/1000/1000}ms")
  }

  // helper functions
  implicit class symbolSeq(x: Iterable[smt.Symbol]) {
    def prefix(p: String): Iterable[smt.Symbol] = x.map(s => smt.Symbol(p + s.id, s.typ))
    def suffix(suf: String): Iterable[smt.Symbol] = x.map(s => smt.Symbol(s.id + suf, s.typ))
  }
}

object substituteSmt {
  def apply(expr: smt.Expr, map: Map[smt.Expr, smt.Expr]): smt.Expr = map.getOrElse(expr, { expr match {
    case e : smt.Symbol => e
    case e : smt.OperatorApplication => e.copy(operands = e.operands.map(apply(_, map)))
    case e : smt.Literal => e
    case s : smt.ArraySelectOperation => s.copy(e = apply(s.e, map), index = s.index.map(apply(_, map)))
    case s : smt.ArrayStoreOperation => s.copy(e = apply(s.e, map), index = s.index.map(apply(_, map)), value = apply(s.value, map))
    case other => throw new NotImplementedError(s"TODO: deal with $other")
  }})

}

object VerificationTask {
  /** starts in initial state and advances one step with reset = 1 and every other input with an arbitrary value */
  def getResetState(sys: smt.SymbolicTransitionSystem): Map[smt.Symbol, smt.Expr] = {
    val inits = sys.states.map {
      case smt.State(sym, Some(init), _) => sym -> init
      case smt.State(sym, None, _) => sym -> smt.Symbol(sym.id + ".init", sym.typ)
    }.toMap
    // TODO: don't hardcode reset
    val inputs = sys.inputs.map { sym => sym -> (if(sym.id == "reset") smt.BooleanLit(true) else sym) }.toMap
    val subs: Map[smt.Expr, smt.Expr] = inits ++ inputs
    sys.states.map {
      case smt.State(sym, _, Some(next)) => sym -> substituteSmt(next, subs)
      case smt.State(sym, _, None) => sym -> smt.Symbol(sym.id + ".aux", sym.symbolTyp)
    }.toMap
  }
}