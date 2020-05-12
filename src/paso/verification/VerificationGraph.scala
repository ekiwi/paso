// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import java.io.FileWriter

import chisel3.util.log2Ceil

import scala.sys.process._
import paso.chisel.{SMTHelpers, SMTSimplifier}
import uclid.smt
import uclid.smt.{BVGTUOp, ConjunctionOp}

import scala.collection.mutable

object VerificationGraph extends SMTHelpers {
  def merge(a: StepNode, b: StepNode): StepNode = {
    assert(!a.isFork && !b.isFork)
    assert(a.id == 0 && b.id == 0)
    a.next.foreach { aNext =>
      b.next.foreach { bNext =>
        val mutuallyExlusive = Checker.isUnsat(and(aNext.constraintExpr, bNext.constraintExpr))
        assert(mutuallyExlusive, "We currently require all methods to have distinguishing inputs on the first cycle.")
      }
    }
    StepNode(a.next ++ b.next, a.methods | b.methods, 0, isFork = false)
  }

}

case class ForkNode(ii: Int, guard: smt.Expr, method: String)
class VerificationTreeEncoder(check: BoundedCheckBuilder, guards: Map[String, smt.Expr]) extends SMTHelpers {

  case class State(ii: Int, pathGuard: smt.Expr)
  def run(proto: StepNode): Seq[ForkNode] = {
    visit(proto, State(-1, tru))
    forkNodes
  }

  private var branchCounter: Int = 0
  private def getUniqueBranchSymbols(choices: Int): Seq[smt.Symbol] = {
    val base = s"branch_${branchCounter}_c"
    branchCounter += 1
    val names = (0 until choices).map(ii => base + ii.toString)
    names.map(smt.Symbol(_, smt.BoolType))
  }
  private val forkNodes = mutable.ArrayBuffer[ForkNode]()

  private def addForkNode(node: StepNode, state: State): Unit = {
    assert(node.methods.size == 1, "Only a single method allowed in fork node!")
    forkNodes += ForkNode(state.ii, state.pathGuard, node.methods.head)
  }

  private def assumeAt(state: State, e: smt.Expr): Unit = check.assumeAt(state.ii, implies(state.pathGuard, e))
  private def assertAt(state: State, e: smt.Expr): Unit = check.assertAt(state.ii, implies(state.pathGuard, e))

  private def visit(node: StepNode, oldState: State): Unit = {
    val state = oldState.copy(ii = oldState.ii + 1)
    if(node.isFork) { addForkNode(node, state) }
    if(node.isFinal) { return }

    // either of the following input constraints could be true
    val inputConstraints = node.next.map { ii =>
      // add method guard if necessary
      if(ii.methods.size > 1 || ii.methods != node.methods || state.ii == 0) {
        val g = ii.methods.toSeq.map(guards).filterNot(_ == tru)
        if(g.nonEmpty) {
          and(ii.constraintExpr, disjunction(g))
        } else {
          ii.constraintExpr
        }
      } else {
        ii.constraintExpr
      }
    }
    assumeAt(state, disjunction(inputConstraints))

    if(node.isBranchPoint) {
      val syms = getUniqueBranchSymbols(node.next.length)
      node.next.zip(syms).foreach { case (input, sym) =>
        // associate path with a symbol
        check.assumeAt(state.ii, iff(sym, and(state.pathGuard, input.constraintExpr)))
        visit(input, state.copy(pathGuard = sym))
      }
    } else {
      visit(node.next.head, state)
    }
  }

  private def visit(node: InputNode, state: State): Unit = {
    assert(!node.isFinal, "Should never end on an input node. Expecting an empty output node to follow.")
    if(node.mappings.nonEmpty) { check.assumeAt(state.ii, implies(state.pathGuard, node.mappingExpr)) }

    // at least one of the following output constraints has to be true
    assertAt(state,  disjunction(node.next.map(o => and(o.constraintExpr, o.mappingExpr))))

    if(node.isBranchPoint) {
      val syms = getUniqueBranchSymbols(node.next.length)
      node.next.zip(syms).foreach { case (output, sym) =>
        // associate path with a symbol
        check.assumeAt(state.ii, iff(sym, and(state.pathGuard, output.constraintExpr)))
        visit(output, state.copy(pathGuard = sym))
      }
    } else {
      visit(node.next.head, state)
    }
  }

  private def visit(node: OutputNode, state: State): Unit = {
    assert(!node.isFinal, "OutputNodes not followed by a StepNode are no longer supported!")
    assert(!node.isBranchPoint, "Cannot branch on steps! No way to distinguish between steps.")
    visit(node.next.head, state)
  }
}


case class PipelineAutomatonEncoder(spec: Spec) {
  case class Loc(proto: String, id: Int, isFork: Boolean, isFinal: Boolean) {
    override def toString: String = proto + "@" + id
  }
  private def toLoc(proto: String, node: StepNode): Loc = Loc(proto, node.id, node.isFork, node.isFinal)
  private def findSucessors(node: StepNode): Seq[StepNode] = node.next.flatMap(_.next.flatMap(_.next))
  private def findSteps(node: StepNode): Seq[StepNode] = {
    Seq(node) ++ node.next.flatMap(_.next.flatMap(_.next.flatMap(findSteps)))
  }
  private val locIndex: Map[Loc, StepNode] = spec.protocols.flatMap { case (name, step) =>
    findSteps(step).map(s => toLoc(name, s) -> s)
  }
  private val nextLoc: Map[Loc, Seq[Loc]] = spec.protocols.flatMap { case (name, step) =>
    findSteps(step).map(s => toLoc(name, s) -> findSucessors(s).map(x => toLoc(name, x)))
  }
  nextLoc.foreach(l => assert(l._2.length <= 1, "TODO: handle branches correctly!"))
  case class InstanceLoc(instance: Int, loc: Loc) {
    override def toString: String = loc.proto + "'" + instance + "@" + loc.id
  }
  private val instanceCount = mutable.HashMap(spec.protocols.keys.map(_ -> 0).toSeq: _*)
  case class State(active: Seq[InstanceLoc], isFork: Boolean) {
    override def toString: String = "{" + active.map(_.toString).sorted.mkString(", ") + "}" + (if(isFork) " (F)" else "")
  }
  private val states = mutable.HashMap[String, State]()
  private val nextState = mutable.ArrayBuffer[Edge]()

  case class Edge(from: State, to: State, active: Seq[InstanceLoc]) {
    override def toString: String = from + " -> " + to + " : {" + active.map(_.toString).sorted.mkString(", ") + "}"
  }

  /** returns the id of a free instance of the protocol specified */
  def getFreeInstance(active: Seq[InstanceLoc], proto: String): Int = {
    val activeIds = active.filter(_.loc.proto == proto).map(_.instance).toSet
    val smallestId = (0 until 100).find(ii => !activeIds.contains(ii)).get
    // ensure that the instance count is correct
    if(instanceCount(proto) <= smallestId) instanceCount(proto) = smallestId + 1
    smallestId
  }

  def executeState(st: State): Unit = {
    println(s"executeState($st)")

    val newLocs = if(!st.isFork) Seq(Seq()) else {
      spec.protocols.map { case (proto, step) =>
        val id = getFreeInstance(st.active, proto)
        Seq(InstanceLoc(id, toLoc(proto, step)))
      }
    }.toSeq

    newLocs.foreach { nl =>
      if(nl.nonEmpty) println(s"FORK: ${nl.head}")
      val currentLocs = nl ++ st.active
      val nextLocs: Seq[InstanceLoc] = currentLocs.flatMap(loc => nextLoc(loc.loc).map(InstanceLoc(loc.instance, _)))
      val isFork = nextLocs.exists(_.loc.isFork)
      val active = nextLocs.filterNot(_.loc.isFinal)
      val next = State(active, isFork)
      // check if this state already exists
      val alreadyVisited = states.contains(next.toString)
      val uniqueNext = states.getOrElseUpdate(next.toString, next)
      // describe the edge
      val e = Edge(st, uniqueNext, currentLocs)
      nextState.append(e)
      if(!alreadyVisited) {
        executeState(uniqueNext)
      }
    }
  }

  // TODO: check that all protocols (including the guard) are mutually exclusive
  def run(): Unit = {
    val initState = State(Seq(), isFork = true)
    states(initState.toString) = initState
    executeState(initState)
    println(s"${nextState.size} edges, ${states.size} nodes")
    println()
  }
}


case class VerificationAutomatonEncoder(methodFuns: Map[smt.Symbol, smt.FunctionApplication], modelState: Seq[smt.Symbol], switchAssumesAndGuarantees: Boolean = false) extends SMTHelpers {
  // TODO: remove simplifications
  private def simplify(e: smt.Expr): smt.Expr = SMTSimplifier.simplify(e)
  private def simplify(e: Seq[smt.Expr]): Seq[smt.Expr] = e.map(SMTSimplifier.simplify).filterNot(_ == tru)

  type StateId = Int
  case class ArgMap(guard: smt.Expr, eq: ArgumentEq)
  case class OutputConstraint(guard: smt.Expr, constraint: smt.Expr)
  case class NextState(guard: smt.Expr, nextId: StateId)
  case class StateUpdate(guard: smt.Expr, state: smt.Symbol, value: smt.Expr)
  case class State(id: StateId,
                   inputMappings: Seq[ArgMap], // mapping DUV inputs to method arguments (depending on input constraints)
                   environmentAssumptions: smt.Expr, // restrict the inputs space
                   nextStates: Seq[NextState], // the next state might depend on inputs and outputs
                   systemAssertions: Seq[OutputConstraint], // expected outputs depending on the input path taken
                   stateUpdates: Seq[StateUpdate], // updates to the architectural state
                  )

  def encodeStatesIntoTransitionSystem(prefix: String, resetAssumption: smt.Expr, start: State, states: Seq[State]): smt.TransitionSystem = {
    // calculate transition function for the "state" state, i.e. the state of our automaton
    val stateBits = log2Ceil(states.length + 1)
    val stateSym = smt.Symbol(prefix + "state", smt.BitVectorType(stateBits))
    def inState(id: Int): smt.Expr = eq(stateSym, smt.BitVectorLit(id, stateBits))

    // if we ever get into this state, we have done something wrong
    val invalidState = smt.BitVectorLit(states.length, stateBits)
    val badInInvalidState = eq(stateSym, invalidState)

    // calculate the next state
    val nextStateAndGuard= states.flatMap(s => s.nextStates.map(n => (n.nextId, and(n.guard, inState(s.id)))))
    val nextState = nextStateAndGuard.groupBy(_._1).foldLeft[smt.Expr](invalidState){ case (other, (stateId, guards)) =>
      ite(disjunction(guards.map(_._2)), smt.BitVectorLit(stateId, stateBits), other)
    }
    val stateState = smt.State(stateSym, init = Some(smt.BitVectorLit(start.id, stateBits)), next = Some(simplify(nextState)))

    // besides the "state" we need to keep track of argument mapped in earlier cycles
    // so that we can use them in output constraints in a later cycle
    // to do this we create a state for every argument
    val mappingsByArgName = states.flatMap(s => s.inputMappings.map((s.id,_))).groupBy(_._2.eq.argRange.sym.id)
    val args = mappingsByArgName.map { case(_, m) =>
      val stateSym = m.head._2.eq.argRange.sym
      val nextArg = m.groupBy(_._1).map { case (state, updates) =>
        // TODO: for now we only support a single full update --> need to implement partial updates at some point
        assert(updates.length == 1)
        assert(updates.head._2.eq.argRange.isFullRange)
        and(inState(state), updates.head._2.guard) -> updates.head._2.eq.range.toExpr()
      }.foldLeft[smt.Expr](stateSym){ case (other, (cond, value)) => ite(cond, value, other) }
      smt.State(stateSym, next = Some(simplify(nextArg)))
    }

    // we also need to keep track of the architectural state of the untimed model
    val updatesByState = states.flatMap(s => s.stateUpdates.map((s.id, _))).groupBy(_._2.state.id)
    val untimedState = updatesByState.map { case (_, u) =>
      val stateSym = u.head._2.state
      val nextState = u.map { case (state, update) =>
        and(inState(state), update.guard) -> update.value
      }.foldLeft[smt.Expr](stateSym){ case (other, (cond, value)) => ite(cond, value, other) }
      smt.State(stateSym, next = Some(simplify(nextState)))
      // TODO: add option to init the state (for bmc)
    }

    val assumptions = states.map(s => implies(inState(s.id), s.environmentAssumptions)) ++ Seq(resetAssumption)
    val guarantees = states.flatMap(s => s.systemAssertions.map(a => implies(inState(s.id), implies(a.guard, a.constraint))))

    val assumptionsSimple = simplify(assumptions)
    val guaranteesSimple  = simplify(guarantees)

    // turn environment assumptions or system assertions into constraints
    val constraints = if(switchAssumesAndGuarantees) guaranteesSimple else assumptionsSimple

    // turn system assertions or environment assumptions into bad states (requires negation)
    val asserts = if(switchAssumesAndGuarantees) assumptionsSimple else guaranteesSimple
    val bads = asserts.map(not)

    smt.TransitionSystem(
      name = Some(prefix.dropRight(1)),
      inputs = Seq(),
      states = Seq(stateState) ++ args ++ untimedState,
      constraints = constraints,
      bad = Seq(badInInvalidState) ++ bads
    )
  }

  def run(proto: StepNode, prefix: String, resetAssumption: smt.Expr): smt.TransitionSystem = {
    val start_id = visit(proto)
    val start = states.find(_.id == start_id).get
    encodeStatesIntoTransitionSystem(prefix, resetAssumption, start, states)
  }

  private val StartId: StateId = 0
  private var stateCounter: Int = StartId
  private val states = mutable.ArrayBuffer[State]()
  private def getStateId: StateId = { val ii = stateCounter; stateCounter += 1; ii}

  private def visit(node: StepNode): StateId = {
    if(node.isFinal) { return StartId }

    val id = getStateId

    // either of the following input constraints could be true
    val environmentAssumptions = disjunction(node.next.map(_.constraintExpr))

    // TODO: in case there is an input branch, identifying the disagreeing constraint that separates
    //       the branches would lead to a smaller formula,
    //       i.e. a -> x and b -> y instead of (a and c) -> x and (b and c) -> y
    val inputGuards = if(node.isBranchPoint) { node.next.map(_.constraintExpr) } else { Seq(tru) }

    val ir = node.next.zip(inputGuards).map { case (input, inGuard) => visit(inGuard, input) }
    val inputMappings = ir.flatMap(_._1)
    val systemAssertions = ir.flatMap(_._2)
    val nextState = ir.flatMap(_._3)
    val stateUpdates = ir.flatMap(_._4)

    val s = State(id, inputMappings, environmentAssumptions, nextState, systemAssertions, stateUpdates)
    states.append(s)
    s.id
  }

  def visit(inGuard: smt.Expr, node: InputNode): (Seq[ArgMap], Seq[OutputConstraint], Seq[NextState], Seq[StateUpdate]) = {
    val mappings = node.mappings.map(ArgMap(inGuard, _))

    // at least one of the following output constraints has to be true
    val systemAssertion = disjunction(node.next.map(_.constraintExpr))

    // TODO: in case there is an input branch, identifying the disagreeing constraint that separates
    //       the branches would lead to a smaller formula,
    //       i.e. a -> x and b -> y instead of (a and c) -> x and (b and c) -> y
    // note that return argument maps cannot be used to distinguish the path
    val outputGuards = if(node.isBranchPoint) { node.next.map(o => and(inGuard, o.constraintExpr)) } else { Seq(inGuard) }
    val nextStatesAndMappingsAndUpdates = node.next.zip(outputGuards).map{
      case(output, outGuard) => visit(outGuard, mappings, output)
    }

    val constraints = Seq(OutputConstraint(inGuard, systemAssertion)) ++ nextStatesAndMappingsAndUpdates.flatMap(_._2)
    val nextStates = nextStatesAndMappingsAndUpdates.map(_._1)
    val stateUpdates = nextStatesAndMappingsAndUpdates.flatMap(_._3)
    (mappings, constraints, nextStates, stateUpdates)
  }

  def visit(outGuard: smt.Expr, inputMap: Seq[ArgMap], node: OutputNode): (NextState, Seq[OutputConstraint], Seq[StateUpdate]) = {
    assert(!node.isBranchPoint, "Cannot branch on steps! No way to distinguish between steps.")
    assert(!node.isFinal, "TODO: deal with final output nodes")

    val mappings = node.mappings.map { m =>
      // substitute argument to refer to the correct mapping
      val argValue = callWithLatestArgumentValue(methodFuns(m.argRange.sym), inputMap)
      val guard = smt.Symbol(m.argRange.sym.id + ".valid", smt.BoolType)
      val guardValue = callWithLatestArgumentValue(methodFuns(guard), inputMap)
      // build constraint expressions
      val argExpr = if(m.argRange.isFullRange) argValue else app(smt.BVExtractOp(hi=m.argRange.hi, lo=m.argRange.lo), argValue)
      val equality = eq(m.range.toExpr(), argExpr)
      OutputConstraint(outGuard, implies(guardValue, equality))
    }

    val next = NextState(outGuard, visit(node.next.head))

    // if this is the last node before going back into the idle state --> commit any updates to the architectural state
    val updates = if(node.next.head.isFinal) {
      assert(node.methods.size == 1, "Cannot have overlapping methods at the commit point!")
      val meth = node.methods.head

      // find all state updates for this method
      modelState.map { state =>
        val stateUpdate = state.copy(id = state.id + s".$meth")
        val updateValue = callWithLatestArgumentValue(methodFuns(stateUpdate), inputMap)
        StateUpdate(outGuard, state, updateValue)
      }
    } else { Seq() }

    (next, mappings, updates)
  }

  private def callWithLatestArgumentValue(foo: smt.FunctionApplication, map: Seq[ArgMap]): smt.FunctionApplication = {
    val args = foo.args.map(a => getLatestArgumentValue(a.asInstanceOf[smt.Symbol], map))
    foo.copy(args = args)
  }

  /** Returns the argument state if the argument is not mapped in the current cycle. */
  private def getLatestArgumentValue(arg: smt.Symbol, map: Seq[ArgMap]): smt.Expr = {
    // TODO: for now we only support a single full update --> need to implement partial updates at some point
    assert(map.forall(_.eq.argRange.isFullRange))
    map.find(_.eq.argRange.sym == arg).map(_.eq.range.toExpr()).getOrElse(arg)
  }
}

object Checker extends SMTHelpers with HasSolver {
  val solver = new YicesInterface
  def isSat(e: smt.Expr): Boolean = check(e).isTrue
  def isUnsat(e: smt.Expr): Boolean = check(e).isFalse
  def isValid(e: smt.Expr): Boolean = isUnsat(app(smt.NegationOp, e))
}

trait HasSolver {
  val solver: Solver
  def check(e: smt.Expr): smt.SolverResult = solver.check(e)
}

object VerificationGraphToDot extends SMTHelpers {
  type Arrows = Seq[(VerificationNode, VerificationNode, String)]

//  private def visit(node: PendingInputNode): Arrows = node.next.flatMap(visit(_, node))
//  private def visit(node: PendingOutputNode): Arrows = node.next.flatMap(visit(_, node))
//  private def mkMsg(constraints: Seq[smt.Expr], mappings: Seq[smt.Expr]): String = {
//    (constraints ++ mappings).map(SMTSimplifier.simplify).mkString(", ")
//  }
//  private def visit(edge: InputEdge, parent: VerificationNode): Arrows = {
//    val msg = mkMsg(edge.constraints, edge.mappings)
//    Seq((parent, edge.next, msg)) ++ visit(edge.next)
//  }
//  private def visit(edge: OutputEdge, parent: VerificationNode): Arrows = {
//    val msg = mkMsg(edge.constraints, edge.mappings)
//    Seq((parent, edge.next, msg)) ++ visit(edge.next)
//  }

  def apply(name: String, graph: StepNode): String = ???
//  {
//    val arrows = visit(graph)
//    val edges = arrows.flatMap(a => Set(a._1, a._2)).toSet
//    val edgeToId = edges.zipWithIndex.toMap
//    val edgeIds = edgeToId.values
//
//    val nodes = edgeIds.map(i => s"$i [shape=point]").mkString("\n")
//    val connections = arrows.map(a => s"""${edgeToId(a._1)} -> ${edgeToId(a._2)} [label="${a._3}"]""").mkString("\n")
//
//    s"""
//      |digraph $name {
//      |  rankdir="LR";
//      |  $nodes
//      |  $connections
//      |}
//      |""".stripMargin
//  }
}

object ShowDot {
  def apply(src: String, fileName: String = "test.dot"): Unit = {
    val ff = new FileWriter(fileName)
    ff.write(src)
    ff.close()
    s"xdot $fileName"!!
  }
}