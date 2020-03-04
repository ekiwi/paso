// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import paso.chisel.SmtHelpers
import uclid.smt
import uclid.smt.ConjunctionOp

object VerificationGraph extends SmtHelpers {
  lazy val solver = new smt.SMTLIB2Interface(List("yices-smt2"))
  def isFinalState(n: PendingInputNode): Boolean = n.next.isEmpty


  def compareEdges(a: VerificationEdge, b: VerificationEdge) = {
    // TODO: include mappings only for output edges
    //val ae = (a.constraints ++ a.mappings)
  }

  def merge(a: PendingInputNode, b: PendingInputNode): Unit = {
    //if(isFinalState(a) || isFinalState(b)) assert(a.)


  }

}

object Checker extends SmtHelpers {
  private lazy val solver = new smt.SMTLIB2Interface(List("yices-smt2"))
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
