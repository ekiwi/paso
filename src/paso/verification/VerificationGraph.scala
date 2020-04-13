// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import java.io.FileWriter
import scala.sys.process._

import paso.chisel.{SMTSimplifier, SmtHelpers}
import uclid.smt
import uclid.smt.ConjunctionOp

object VerificationGraph extends SmtHelpers {
  lazy val solver = new smt.SMTLIB2Interface(List("yices-smt2"))
  private def isFinalState(n: PendingInputNode): Boolean = n.next.isEmpty

  private def not(exprs: Seq[smt.Expr]): Seq[smt.Expr] = exprs.map(app(smt.NegationOp, _))

  private def getConstraints(e: VerificationEdge): smt.Expr = e match {
    // for input edges, variable mappings are not constraints
    case InputEdge(constraints, _, _, _) => conjunction(constraints)
    // for output edges we over-approximate by treating output mappings as constraints
    case OutputEdge(constraints, mappings, _, _) => conjunction(constraints ++ mappings)
  }

  // combine two edges into all three combinations
  private def combineEdges[E <: VerificationEdge](a: E, b: E): (E, E, E) = (a, b) match {
    case (a: InputEdge, b: InputEdge) => val (x,y,z) = combineEdges(a, b) ; (x.asInstanceOf[E], y.asInstanceOf[E], z.asInstanceOf[E])
    case (a: OutputEdge, b: OutputEdge) => val (x,y,z) = combineEdges(a, b) ; (x.asInstanceOf[E], y.asInstanceOf[E], z.asInstanceOf[E])
  }
  private def combineEdges(a: InputEdge, b: InputEdge): (InputEdge, InputEdge, InputEdge) = (
    // a /\ b
    InputEdge(a.constraints ++ b.constraints, a.mappings ++ b.mappings, a.methods | b.methods, merge(a.next, b.next)),
    // a /\ ~b
    InputEdge(a.constraints ++ not(b.constraints), a.mappings, a.methods, a.next),
    // a~ /\ b
    InputEdge(not(a.constraints) ++ b.constraints, b.mappings, b.methods, b.next)
  )
  private def combineEdges(a: OutputEdge, b: OutputEdge): (OutputEdge, OutputEdge, OutputEdge) = (
    // a /\ b
    OutputEdge(a.constraints ++ b.constraints, a.mappings ++ b.mappings, a.methods | b.methods, merge(a.next, b.next)),
    // a /\ ~b
    OutputEdge(a.constraints ++ not(b.constraints), a.mappings, a.methods, a.next),
    // a~ /\ b
    OutputEdge(not(a.constraints) ++ b.constraints, b.mappings, b.methods, b.next)
  )

  // returns old or new edge plus remaining edge that needs to be merged
  // maintains the invariance that all outgoing edges of a node are mutually exclusive
  private def mergeEdge(old: InputEdge, new_edge: Option[InputEdge]): (Seq[InputEdge], Option[InputEdge]) = {
    // fast exit for empty new edge
    if(new_edge.isEmpty) { return (Seq(old), None) }

    // generate constraints (these depend on the type of the edge)
    val (old_con, new_con) = (getConstraints(old), getConstraints(new_edge.get))

    // if the edge constraints are mutually exclusive, there is nothing to do
    if(Checker.isUnsat(and(old_con, new_con))) { return (Seq(old), Some(new_edge.get)) }

    // merge the two edges
    val (o_and_n, o_and_not_n, not_o_and_n) = combineEdges(old, new_edge.get)

    // merged edges
    val edges = if(Checker.isSat(and(old_con, not(new_con)))) { Seq(o_and_n, o_and_not_n) } else { Seq(o_and_n) }

    // remaining edge
    val remaining = if(Checker.isSat(and(not(old_con), new_con))) { Some(not_o_and_n) } else { None }

    (edges, remaining)
  }

  private def mergeEdge(old: OutputEdge, new_edge: Option[OutputEdge]): (Seq[OutputEdge], Option[OutputEdge]) = {
    // fast exit for empty new edge
    if(new_edge.isEmpty) { return (Seq(old), None) }

    throw new NotImplementedError("TODO: merge output edges!")

    assert((new_edge.get.methods & old.methods).isEmpty, "Should only merge graphs from different methods")


    // now we need to check that the edges don't impose any constraints on each other



    (Seq(), None) // FIXME
  }


//  private def mergeEdge[E <: VerificationEdge](edges: Seq[E], edge: E): Seq[E] = {
//    var new_edge: Option[E] = Some(edge)
//    val new_edges = edges.flatMap { old =>
//      val res = mergeEdge(old, new_edge)
//      new_edge = res._2
//      res._1
//    }
//    new_edge match {
//      case None => new_edges
//      case Some(e) => new_edges ++ Seq(e)
//    }
//  }

  private def mergeEdge(edges: Seq[InputEdge], edge: InputEdge): Seq[InputEdge] = {
    var new_edge: Option[InputEdge] = Some(edge)
    val new_edges = edges.flatMap { old =>
      val res = mergeEdge(old, new_edge)
      new_edge = res._2
      res._1
    }
    new_edge match {
      case None => new_edges
      case Some(e) => new_edges ++ Seq(e)
    }
  }

  private def mergeEdge(edges: Seq[OutputEdge], edge: OutputEdge): Seq[OutputEdge] = {
    var new_edge: Option[OutputEdge] = Some(edge)
    val new_edges = edges.flatMap { old =>
      val res = mergeEdge(old, new_edge)
      new_edge = res._2
      res._1
    }
    new_edge match {
      case None => new_edges
      case Some(e) => new_edges ++ Seq(e)
    }
  }

  def merge(a: PendingInputNode, b: PendingInputNode): PendingInputNode = {
    var next = a.next
    b.next.foreach { new_edge => next = mergeEdge(next, new_edge) }
    PendingInputNode(next)
  }

  private def merge(a: PendingOutputNode, b: PendingOutputNode): PendingOutputNode = {
    var next = a.next
    b.next.foreach { new_edge => next = mergeEdge(next, new_edge) }
    PendingOutputNode(next)
  }

}

object Checker extends SmtHelpers with HasSolver {
  val solver = new YicesInterface
  def isSat(e: smt.Expr): Boolean = check(e).isTrue
  def isUnsat(e: smt.Expr): Boolean = check(e).isFalse
  def isValid(e: smt.Expr): Boolean = isUnsat(app(smt.NegationOp, e))
}

trait HasSolver {
  val solver: Solver
  def check(e: smt.Expr): smt.SolverResult = solver.check(e)
}

object VerificationGraphToDot extends SmtHelpers {
  type Arrows = Seq[(VerificationNode, VerificationNode, String)]

  private def visit(node: PendingInputNode): Arrows = node.next.flatMap(visit(_, node))
  private def visit(node: PendingOutputNode): Arrows = node.next.flatMap(visit(_, node))
  private def mkMsg(constraints: Seq[smt.Expr], mappings: Seq[smt.Expr]): String = {
    (constraints ++ mappings).map(SMTSimplifier.simplify).mkString(", ")
  }
  private def visit(edge: InputEdge, parent: VerificationNode): Arrows = {
    val msg = mkMsg(edge.constraints, edge.mappings)
    Seq((parent, edge.next, msg)) ++ visit(edge.next)
  }
  private def visit(edge: OutputEdge, parent: VerificationNode): Arrows = {
    val msg = mkMsg(edge.constraints, edge.mappings)
    Seq((parent, edge.next, msg)) ++ visit(edge.next)
  }

  def apply(name: String, graph: PendingInputNode): String = {
    val arrows = visit(graph)
    val edges = arrows.flatMap(a => Set(a._1, a._2)).toSet
    val edgeToId = edges.zipWithIndex.toMap
    val edgeIds = edgeToId.values

    val nodes = edgeIds.map(i => s"$i [shape=point]").mkString("\n")
    val connections = arrows.map(a => s"""${edgeToId(a._1)} -> ${edgeToId(a._2)} [label="${a._3}"]""").mkString("\n")

    s"""
      |digraph $name {
      |  rankdir="LR";
      |  $nodes
      |  $connections
      |}
      |""".stripMargin
  }
}

object ShowDot {
  def apply(src: String, fileName: String = "test.dot"): Unit = {
    val ff = new FileWriter(fileName)
    ff.write(src)
    ff.close()
    s"xdot $fileName"!!
  }
}