// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import paso.chisel.SmtHelpers
import uclid.smt
import uclid.smt.ConjunctionOp

object VerificationGraph extends SmtHelpers {
  lazy val solver = new smt.SMTLIB2Interface(List("yices-smt2"))
  private def isFinalState(n: PendingInputNode): Boolean = n.next.isEmpty

  private def not(exprs: Seq[smt.Expr]): Seq[smt.Expr] = exprs.map(app(smt.NegationOp, _))

  private def getConstraints(e: VerificationEdge): smt.Expr = e match {
    // for input edges, variable mappings are not constraints
    case InputEdge(constraints, _, _, _) => Checker.conjunction(constraints)
    // for output edges we over-approximate by treating output mappings as constraints
    case OutputEdge(constraints, mappings, _, _) => Checker.conjunction(constraints ++ mappings)
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
  private def mergeEdge[E <: VerificationEdge](old: E, new_edge: Option[E]): (Seq[E], Option[E]) = {
    // fast exit for empty new edge
    if(new_edge.isEmpty) { return (Seq(old), None) }

    // generate constraints (these depend on the type of the edge)
    val (old_con, new_con) = (getConstraints(old), getConstraints(new_edge.get))

    // if the edge constraints are mutually exclusive, there is nothing to do
    if(Checker.isMutuallyExclusive(old_con, new_con)) { return (Seq(old), Some(new_edge.get)) }

    // merge the two edges
    val (o_and_n, o_and_not_n, not_o_and_n) = combineEdges(old, new_edge.get)

    // merged edges
    val edges = if(Checker.isSat(and(old_con, not(new_con)))) { Seq(o_and_n, o_and_not_n) } else { Seq(o_and_n) }

    // remaining edge
    val remaining = if(Checker.isSat(and(not(old_con), new_con))) { Some(not_o_and_n) } else { None }

    (edges, remaining)
  }

  private def mergeEdge[E <: VerificationEdge](edges: Seq[E], edge: E): Seq[E] = {
    var new_edge: Option[E] = Some(edge)
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

object Checker extends SmtHelpers {
  private lazy val solver = new YicesInterface
  private def check(e: smt.Expr) = {
    solver.push()
    solver.assert(e)
    val res = solver.check()
    solver.pop()
    res
  }
  def isSat(e: smt.Expr): Boolean = check(e).isTrue
  def isUnsat(e: smt.Expr): Boolean = check(e).isFalse
  def isValid(e: smt.Expr): Boolean = isUnsat(app(smt.NegationOp, e))
  def conjunction(c: Seq[smt.Expr]): smt.Expr = c.foldLeft[smt.Expr](smt.BooleanLit(true)){case (a,b) => app(ConjunctionOp, a, b)}
  def equisatisfiable(a: smt.Expr, b:smt.Expr): Boolean = isValid(app(smt.EqualityOp, a, b))
  def aIsSubsetOfB(a: smt.Expr, b: smt.Expr): Boolean = isValid(app(smt.ImplicationOp, a, b))
  def isMutuallyExclusive(a: smt.Expr, b: smt.Expr): Boolean = isValid(app(smt.InequalityOp, a, b))
}
