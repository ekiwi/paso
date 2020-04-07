// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import uclid.smt



trait SmtHelpers {
  def bool_to_bv(b: smt.Expr): smt.Expr = b match {
    case smt.BooleanLit(value) => smt.BitVectorLit(if(value) 1 else 0, 1)
    case other => ite(other, smt.BitVectorLit(1,1), smt.BitVectorLit(0,1))
  }
  def as_bv(e: smt.Expr): smt.Expr = e.typ match {
    case smt.BoolType => bool_to_bv(e)
    case smt.BitVectorType(_) => e
    case other => throw new RuntimeException(s"$other cannot be converted to a bitvector")
  }
  def app(op: smt.Operator, exprs: smt.Expr*) = smt.OperatorApplication(op, exprs.toList)
  def arrayIndexBits(array: smt.Expr): Int = {
    require(array.typ.isArray)
    require(array.typ.asInstanceOf[smt.ArrayType].inTypes.length == 1)
    require(array.typ.asInstanceOf[smt.ArrayType].inTypes.head.isBitVector)
    array.typ.asInstanceOf[smt.ArrayType].inTypes.head.asInstanceOf[smt.BitVectorType].width
  }
  def select(array: smt.Expr, index: smt.Expr) = smt.ArraySelectOperation(array, List(index))
  def select(array: smt.Expr, index: BigInt) = {
    smt.ArraySelectOperation(array, List(smt.BitVectorLit(index, arrayIndexBits(array))))
  }
  def store(array: smt.Expr, index: smt.Expr, value: smt.Expr) = smt.ArrayStoreOperation(array, List(index), value)
  def store(array: smt.Expr, index: BigInt, value: smt.Expr) = {
    smt.ArrayStoreOperation(array, List(smt.BitVectorLit(index, arrayIndexBits(array))), value)
  }
  def ext(expr: smt.Expr, width: Int, op: (Int, Int) => smt.Operator) = {
    val bv_expr = as_bv(expr)
    val w = bv_expr.typ.asInstanceOf[smt.BitVectorType].width
    val e = width - w
    require(e >= 0)
    if(e == 0) expr else app(op(width, e), bv_expr)
  }
  def zext(expr: smt.Expr, width: Int): smt.Expr = ext(expr, width, (w, e) => smt.BVZeroExtOp(w, e))
  def sext(expr: smt.Expr, width: Int): smt.Expr = ext(expr, width, (w, e) => smt.BVSignExtOp(w, e))
  def ite(cond: smt.Expr, tru: smt.Expr, fals: smt.Expr): smt.Expr = app(smt.ITEOp, cond, tru, fals)
  def and(exprs: smt.Expr*): smt.Expr = exprs.reduceLeft((a,b) => app(smt.ConjunctionOp, a, b))
  def or(exprs: smt.Expr*): smt.Expr = exprs.reduceLeft((a,b) => app(smt.DisjunctionOp, a, b))
  def not(expr: smt.Expr): smt.Expr = app(smt.NegationOp, expr)
  def eq(a: smt.Expr, b: smt.Expr): smt.Expr = app(smt.EqualityOp, a, b)
  def iff(a: smt.Expr, b: smt.Expr): smt.Expr = app(smt.IffOp, a, b)
  def neq(a: smt.Expr, b: smt.Expr): smt.Expr = app(smt.InequalityOp, a, b)
  def implies(a: smt.Expr, b: smt.Expr): smt.Expr = app(smt.ImplicationOp, a, b)
  def conjunction(c: Iterable[smt.Expr]): smt.Expr = c.foldLeft[smt.Expr](smt.BooleanLit(true)){case (a,b) => app(smt.ConjunctionOp, a, b)}
  def disjunction(c: Iterable[smt.Expr]): smt.Expr = c.foldLeft[smt.Expr](smt.BooleanLit(false)){case (a,b) => app(smt.DisjunctionOp, a, b)}
  def forall(vars: Seq[smt.Symbol], e: smt.Expr): smt.Expr = vars.foldRight(e)((vv, e) => app(smt.ForallOp(List(vv), List()), e))
  val tru = smt.BooleanLit(true)
  val fals = smt.BooleanLit(false)
  def getBits(typ: smt.Type) = typ match {
    case smt.BoolType => 1
    case smt.BitVectorType(w) => w
  }
}

object SmtHelper extends SmtHelpers {

}