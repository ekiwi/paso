// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

// contains data structures used for verification
// mostly language neutral (aka Chisel independent)

package paso.verification

import paso.chisel.{SMTSimplifier, SmtHelpers}
import uclid.smt
import uclid.smt.Expr

import scala.collection.mutable

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

trait Assertion { def toExpr: smt.Expr }
case class BasicAssertion(guard: smt.Expr, pred: smt.Expr) extends Assertion with SmtHelpers {
  override def toExpr: Expr = implies(guard, pred)
}
case class ForAllAssertion(variable: smt.Symbol, start: Int, end: Int, guard: smt.Expr, pred: smt.Expr) extends Assertion with SmtHelpers {
  override def toExpr: Expr = {
    val max = 1 << getBits(variable.typ)
    val isFullRange = start == 0 && end == max
    val g = if(isFullRange) { guard } else {
      and(guard, and(cmpConst(smt.BVGEUOp, variable, start), cmpConst(smt.BVLEUOp, variable, end-1)))
    }
    forall(Seq(variable), implies(g, pred))
  }
}

case class VerificationProblem(
                                impl: smt.TransitionSystem,
                                untimed: UntimedModel,
                                protocols: Map[String, PendingInputNode],
                                invariances: Seq[Assertion],
                                mapping: Seq[Assertion]
)

object VerificationProblem {
  def verify(problem: VerificationProblem): Unit = {
    // first we need to make sure to properly namespace all symbols in the Verification Problem
    val p = NamespaceIdentifiers(problem)
    println(p)
    val tasks = Seq(new VerifyMapping, new VerifyBaseCase, new VerifyMethods(oneAtATime = true))
    tasks.foreach(_.run(p))
  }
}



class VerifyMethods(oneAtATime: Boolean) extends VerificationTask with SmtHelpers {
  override val solverName: String = "btormc"


  private def verifyMethods(p: VerificationProblem, proto: PendingInputNode, methods: Map[String, MethodSemantics]): Unit = {
    val check = new BoundedCheckBuilder(p.impl)

    //ShowDot(VerificationGraphToDot("proto", proto))

    // assume that reset is inactive
    VerificationTask.findReset(p.impl.inputs).foreach(r => check.assume(not(r)))
    // assume that invariances hold in the initial state
    p.invariances.foreach(i => check.assumeAt(0, i.toExpr))
    // assume that the mapping function holds in the initial state
    p.mapping.foreach(m => check.assumeAt(0, m.toExpr))
    // compute the results of all methods
    val method_state_subs = methods.map { case (name, sem) =>
      sem.outputs.foreach{ o => check.define(o.sym, o.expr) }
      sem.outputs.foreach{ o => check.define(smt.Symbol(o.sym.id + ".valid", smt.BoolType), o.guard) }
      sem.updates.suffix(s".$name").foreach{ o => check.define(o.sym, o.expr) }
      name -> sem.updates.map(_.sym).map(s => s -> s.copy(id = s.id + s".$name"))
    }

    // encode the protocol tree
    val final_edges = new VerificationTreeEncoder(check).run(proto)

    // make sure that in the final states the mapping as well as the invariances hold
    final_edges.foreach { case(edge, taken, step) =>
      assert(edge.methods.size == 1)
      // substitute any references to the state of the untimed model with the result of applying the method
      val subs: Map[smt.Expr, smt.Expr] = method_state_subs(edge.methods.head).toMap
      p.invariances.foreach(i => check.assertAt(step, implies(taken, i.toExpr)))
      p.mapping.map(substituteSmt(_, subs)).foreach(m => check.assertAt(step, implies(taken, m.toExpr)))
    }

    val sys = check.getCombinedSystem
    val checker = smt.Btor2.createBtorMC()
    //val checker = smt.Btor2.createCosa2MC()
    val res = checker.check(sys, fileName=Some("test.btor"), kMax = check.getK)

    // find failing property and print
    res match {
      case smt.ModelCheckFail(witness) => new smt.TransitionSystemSimulator(sys).run(witness, Some("test.vcd"))
      case smt.ModelCheckSuccess() =>
    }

    assert(res.isSuccess, s"Failed to verify ${methods.keys.mkString(", ")} on ${p.untimed.name}")
  }

  override protected def execute(p: VerificationProblem): Unit = {
    // first we need to merge the protocol graph to ensure that methods are independent
    // - independence in this case means that for common inputs, the expected outputs are not mutually exclusive
    val combined = p.protocols.values.reduce(VerificationGraph.merge) // this will fail if methods are not independent

    // we can verify each method individually or with the combined method graph
    if(oneAtATime) {
      p.untimed.methods.foreach { case (name, semantics) =>
        verifyMethods(p, p.protocols(name), Map(name -> semantics))
      }
    } else {
      verifyMethods(p, combined, p.untimed.methods)
    }

  }
}

class RefEqHashMap[A <: AnyRef, B] extends scala.collection.mutable.HashMap[A, B] {
  protected override def elemEquals(key1: A, key2: A): Boolean = (key1 eq key2)
}

class VerificationTreeEncoder(check: BoundedCheckBuilder) extends SmtHelpers {

  def run(proto: PendingInputNode): Seq[(VerificationEdge, smt.Symbol, Int)] = {
    visit(proto, ii = 0, guard = tru)
    finalEdges
  }

  private val edges = new RefEqHashMap[VerificationEdge, smt.Symbol]()
  private def edgeSymbol(i: VerificationEdge): smt.Symbol = edges.getOrElseUpdate(i, {
    smt.Symbol(s"${i.getClass.getSimpleName}_${edges.size}", smt.BoolType)
  })

  private val finalEdges = mutable.ArrayBuffer[(VerificationEdge, smt.Symbol, Int)]()

  private def visit(state: PendingInputNode, ii: Int, guard: smt.Expr): Unit = if(state.next.nonEmpty) {
    // input constraints
    val I = state.next.map{ e => conjunction(e.constraints) }
    // restrict input space to any available edge
    check.assumeAt(ii, implies(guard, disjunction(I)))

    // the edge symbol is true, iff the edge is taken
    state.next.zip(I).foreach { case (edge, const) => check.assumeAt(ii, iff(edgeSymbol(edge), and(guard, const))) }

    // map arguments only if input constraints match
    state.next.collect { case e if e.mappings.nonEmpty =>
      check.assumeAt(ii, implies(edgeSymbol(e), conjunction(e.mappings)))
    }

    // visit intermediate states
    state.next.foreach { e => visit(e.next, ii, guard = edgeSymbol(e)) }
  }

  private def visit(state: PendingOutputNode, ii: Int, guard: smt.Expr): Unit = if(state.next.nonEmpty) {
    // output constraints (for outputs tha mappings can be interpreted as constraints
    val O = state.next.map{ e => conjunction(e.constraints ++ e.mappings) }
    // assert that one of the possible output edges is used
    check.assertAt(ii, implies(guard, disjunction(O)))

    // the edge symbol is true, iff the edge is taken
    state.next.zip(O).foreach { case (edge, const) => check.assumeAt(ii, iff(edgeSymbol(edge), and(guard, const))) }

    // visit next states
    state.next.foreach { e => visit(e.next, ii + 1, guard = edgeSymbol(e)) }

    // remember final edges
    finalEdges ++= state.next.filter(_.next.next.isEmpty).map(e => (e, edgeSymbol(e), ii + 1))
  }
}

class VerifyMapping extends VerificationTask with SmtHelpers with HasSolver {
  val solver = new CVC4Interface(quantifierFree = false)
  override val solverName: String = solver.name

  override protected def execute(p: VerificationProblem): Unit = {
    if(p.mapping.isEmpty) return // early return for empty mapping
    val impl_states = p.impl.states.map(_.sym)
    val impl_init_const = conjunction(VerificationTask.getResetState(p.impl).map{ case (sym, value) => eq(sym, value)} )
    val spec_states = p.untimed.state.map(_.sym)
    val spec_init_const = conjunction(p.untimed.state.map{st => eq(st.sym, st.init.get)})
    val mapping_const = conjunction(p.mapping.map(_.toExpr))

    // The mapping check gets a lot easier because we require the untimed model to have all states initialized
    // to a concrete value, thus eliminating all quantifiers. (the non general solution)
    val use_general_solution = false
    if(use_general_solution) {
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
    } else {
      // With only a single initial specification state we need to show that for all initial implementation
      // states the mapping holds. We turn the universal into a existential query through the standard negation.
      val query = SMTSimplifier.simplify(and(and(impl_init_const, spec_init_const), not(mapping_const)))
      val res = check(query)
      assert(res.isFalse, s"Found a implementation initial state for which there is no mapping: $res")

    }
  }
}

class VerifyBaseCase extends VerificationTask with SmtHelpers with HasSolver {
  val solver = new CVC4Interface
  override val solverName: String = solver.name

  override protected def execute(p: VerificationProblem): Unit = {
    val impl_init_const = conjunction(VerificationTask.getResetState(p.impl).map{ case (sym, value) => eq(sym, value)}.toSeq)
    val inv_const = conjunction(p.invariances.map(_.toExpr))

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
  implicit class namedSeq(x: Iterable[NamedExpr]) {
    def prefix(p: String): Iterable[NamedExpr] = x.map(s => s.copy(sym = s.sym.copy(id = p + s.sym.id)))
    def suffix(p: String): Iterable[NamedExpr] = x.map(s => s.copy(sym = s.sym.copy(id = s.sym.id + p)))
  }
}

object VerificationTask {
  // TODO: don't hardcode reset
  def isReset(sym: smt.Symbol): Boolean = sym.id.endsWith(".reset") && sym.typ.isBool
  def findReset(symbols: Iterable[smt.Symbol]): Option[smt.Symbol] = symbols.find(isReset)
  /** starts in initial state and advances one step with reset = 1 and every other input with an arbitrary value */
  def getResetState(sys: smt.TransitionSystem): Map[smt.Symbol, smt.Expr] = {
    val inits = sys.states.map {
      case smt.State(sym, Some(init), _) => sym -> init
      case smt.State(sym, None, _) => sym -> smt.Symbol(sym.id + ".init", sym.typ)
    }.toMap
    val inputs = sys.inputs.map { sym => sym -> (if(isReset(sym)) smt.BooleanLit(true) else sym) }.toMap
    val subs: Map[smt.Expr, smt.Expr] = inits ++ inputs
    sys.states.map {
      case smt.State(sym, _, Some(next)) => sym -> substituteSmt(next, subs)
      case smt.State(sym, _, None) => sym -> smt.Symbol(sym.id + ".aux", sym.symbolTyp)
    }.toMap
  }
}