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

object VerificationGraph extends SMTHelpers with HasSolver {
  lazy val solver = new CVC4Interface(quantifierFree = true)

  private def not(exprs: Seq[smt.Expr]): Seq[smt.Expr] = exprs.map(app(smt.NegationOp, _))

  // combine two edges into all three combinations
  private def combineInputs(a: InputNode, b: InputNode): (InputNode, InputNode, InputNode) = (
    // a /\ b
    InputNode(mergeOutputs(a.next, b.next), a.methods | b.methods, a.constraints ++ b.constraints, a.mappings ++ b.mappings),
    // a /\ ~b
    a.copy(constraints = a.constraints ++ not(b.constraints)),
    // a~ /\ b
    b.copy(constraints = not(a.constraints) ++ b.constraints)
  )

  // returns old or new node plus remaining node that needs to be merged
  // maintains the invariance that all child nodes are mutually exclusive
  private def mergeInputs(oldNode: InputNode, newNode: Option[InputNode]): (Seq[InputNode], Option[InputNode]) = {
    // fast exit for empty new edge
    if(newNode.isEmpty) { return (Seq(oldNode), None) }

    // generate constraints (these depend on the type of the edge)
    val (oldCon, newCon) = (oldNode.constraintExpr, newNode.get.constraintExpr)

    // if the edge constraints are mutually exclusive, there is nothing to do
    if(Checker.isUnsat(and(oldCon, newCon))) { return (Seq(oldNode), Some(newNode.get)) }

    // merge the two edges
    val (o_and_n, o_and_not_n, not_o_and_n) = combineInputs(oldNode, newNode.get)

    // merged edges
    val edges = if(Checker.isSat(and(oldCon, not(newCon)))) { Seq(o_and_n, o_and_not_n) } else { Seq(o_and_n) }

    // remaining edge
    val remaining = if(Checker.isSat(and(not(oldCon), newCon))) { Some(not_o_and_n) } else { None }

    (edges, remaining)
  }

  private def mergeOutputs(oldNode: OutputNode, newNode: Option[OutputNode]): (Seq[OutputNode], Option[OutputNode]) = {
    // fast exit for empty new edge
    if(newNode.isEmpty) { return (Seq(oldNode), None) }

    throw new NotImplementedError("TODO: merge output edges!")
  }

  private def mergeSingleNode[N <: VerificationNode](aNodes: Seq[N], bNode: N, merge: (N, Option[N]) => (Seq[N], Option[N])): Seq[N] = {
    var newNode: Option[N] = Some(bNode)
    val newNodes = aNodes.flatMap { old =>
      val (newN, remainingN) = merge(old, newNode)
      newNode = remainingN
      newN
    }
    newNode match {
      case None => newNodes
      case Some(e) => newNodes ++ Seq(e)
    }
  }

  private def mergeNodes[N <: VerificationNode](aNodes: Seq[N], bNodes: Seq[N], merge: (N, Option[N]) => (Seq[N], Option[N])): Seq[N] = {
    var newNodes = aNodes
    bNodes.foreach { newN => newNodes = mergeSingleNode(newNodes, newN, merge) }
    newNodes
  }

  private def mergeInputs(a: Seq[InputNode], b: Seq[InputNode]): Seq[InputNode] = mergeNodes(a, b, mergeInputs)
  private def mergeOutputs(a: Seq[OutputNode], b: Seq[OutputNode]): Seq[OutputNode] = mergeNodes(a, b, mergeOutputs)

  def merge(a: StepNode, b: StepNode): StepNode = {
    StepNode(mergeInputs(a.next, b.next), a.methods | b.methods)
  }

}

case class FinalNode(ii: Int, guard: smt.Expr, method: String, isStep: Boolean)
class VerificationTreeEncoder(check: BoundedCheckBuilder, guards: Map[String, smt.Expr]) extends SMTHelpers {

  case class State(ii: Int, pathGuard: smt.Expr)
  def run(proto: StepNode): Seq[FinalNode] = {
    visit(proto, State(-1, tru))
    finalNodes
  }

  private var branchCounter: Int = 0
  private def getUniqueBranchSymbols(choices: Int): Seq[smt.Symbol] = {
    val base = s"branch_${branchCounter}_c"
    branchCounter += 1
    val names = (0 until choices).map(ii => base + ii.toString)
    names.map(smt.Symbol(_, smt.BoolType))
  }
  private val finalNodes = mutable.ArrayBuffer[FinalNode]()

  private def addFinalNode(node: VerificationNode, state: State): Unit = {
    assert(node.next.isEmpty, "Not a final node!")
    assert(node.methods.size == 1, "Only a single method allowed in final node!")
    finalNodes += FinalNode(state.ii, state.pathGuard, node.methods.head, node.isInstanceOf[StepNode])
  }

  private def assumeAt(state: State, e: smt.Expr): Unit = check.assumeAt(state.ii, implies(state.pathGuard, e))
  private def assertAt(state: State, e: smt.Expr): Unit = check.assertAt(state.ii, implies(state.pathGuard, e))

  private def visit(node: StepNode, oldState: State): Unit = {
    val state = oldState.copy(ii = oldState.ii + 1)
    if(node.isFinal) { addFinalNode(node, state); return }

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
    if(node.isFinal) { addFinalNode(node, state); return }
    assert(!node.isBranchPoint, "Cannot branch on steps! No way to distinguish between steps.")
    visit(node.next.head, state)
  }
}

case class VerificationAutomatonEncoder(methodFuns: Map[smt.Symbol, smt.FunctionApplication], switchAssumesAndGuarantees: Boolean = false) extends SMTHelpers {
  // TODO: remove simplifications
  private def simplify(e: smt.Expr): smt.Expr = SMTSimplifier.simplify(e)
  private def simplify(e: Seq[smt.Expr]): Seq[smt.Expr] = e.map(SMTSimplifier.simplify).filterNot(_ == tru)

  type StateId = Int
  case class ArgMap(guard: smt.Expr, eq: ArgumentEq)
  case class OutputConstraint(guard: smt.Expr, constraint: smt.Expr)
  case class NextState(guard: smt.Expr, nextId: StateId)
  case class State(id: StateId,
                   inputMappings: Seq[ArgMap], // mapping DUV inputs to method arguments (depending on input constraints)
                   environmentAssumptions: smt.Expr, // restrict the inputs space
                   nextStates: Seq[NextState], // the next state might depend on inputs and outputs
                   systemAssertions: Seq[OutputConstraint], // expected outputs depending on the input path taken
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
      states = Seq(stateState) ++ args,
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
    if(node.isFinal) {
      if(node.next.isEmpty) {
        return StartId
      } else {
        throw new NotImplementedError("TODO")
      }
    }

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

    val s = State(id, inputMappings, environmentAssumptions, nextState, systemAssertions)
    states.append(s)
    s.id
  }

  def visit(inGuard: smt.Expr, node: InputNode): (Seq[ArgMap], Seq[OutputConstraint], Seq[NextState]) = {
    val mappings = node.mappings.map(ArgMap(inGuard, _))

    // at least one of the following output constraints has to be true
    val systemAssertion = disjunction(node.next.map(_.constraintExpr))

    // TODO: in case there is an input branch, identifying the disagreeing constraint that separates
    //       the branches would lead to a smaller formula,
    //       i.e. a -> x and b -> y instead of (a and c) -> x and (b and c) -> y
    // note that return argument maps cannot be used to distinguish the path
    val outputGuards = if(node.isBranchPoint) { node.next.map(o => and(inGuard, o.constraintExpr)) } else { Seq(inGuard) }
    val nextStatesAndMappings = node.next.zip(outputGuards).map{ case(output, outGuard) => visit(outGuard, mappings, output) }

    val constraints = Seq(OutputConstraint(inGuard, systemAssertion)) ++ nextStatesAndMappings.flatMap(_._2)
    (mappings, constraints, nextStatesAndMappings.map(_._1))
  }

  def visit(outGuard: smt.Expr, inputMap: Seq[ArgMap], node: OutputNode): (NextState, Seq[OutputConstraint]) = {
    assert(!node.isBranchPoint, "Cannot branch on steps! No way to distinguish between steps.")
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
    (next, mappings)
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