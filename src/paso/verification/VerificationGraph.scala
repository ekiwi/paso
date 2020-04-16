// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import java.io.FileWriter

import scala.sys.process._
import paso.chisel.{SMTHelpers, SMTSimplifier}
import uclid.smt
import uclid.smt.ConjunctionOp

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
class VerificationTreeEncoder(check: BoundedCheckBuilder) extends SMTHelpers {

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
    assumeAt(state, disjunction(node.next.map(_.constraintExpr)))

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
    if(node.mappingExpr != tru) { check.assumeAt(state.ii, implies(state.pathGuard, node.mappingExpr)) }

    // at least one of the following output constraints has to be true
    assertAt(state, disjunction(node.next.map(_.constraintExpr)))

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