// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import paso.chisel.SMTSimplifier
import uclid.smt

import scala.collection.mutable

/* eliminates quantifiers by expanding them, thus there might be a significant blowup of the formula
*  TODO: support nested quantifiers
* */
object SMTExpandQuantifiers {
  val expandMax = 2048
  val simplify = true

  private def determineRange(t: smt.Type): Int = t match {
    case smt.BoolType => 2
    case smt.BitVectorType(w) => (1 << w)
    case smt.ArrayType(_, _) => throw new NotImplementedError(s"Currently quantifiers over arrays are not supported")
    case other => throw new RuntimeException(s"Cannot expand quantifier over infinite range: $other")
  }

  private def makeLit(value: BigInt, typ: smt.Type): smt.Expr = typ match {
    case smt.BoolType => smt.BooleanLit(value != 0)
    case smt.BitVectorType(w) => smt.BitVectorLit(value, w)
  }

  private def onExprExpand(e: smt.Expr, v: smt.Symbol, lit: smt.Expr): smt.Expr = e match {
    case o @ smt.OperatorApplication(_ : smt.ForallOp, _) =>
      throw new NotImplementedError(s"Nested quantifiers are not supported: $o")
    case o @ smt.OperatorApplication(_ : smt.ExistsOp, _) =>
      throw new NotImplementedError(s"Nested quantifiers are not supported: $o")
    case x : smt.Symbol if x == v => lit
    case other => other
  }

  private def expand(glue: smt.BoolResultOp, variable: smt.Symbol, e: smt.Expr): smt.Expr = {
    val range = determineRange(variable.typ)
    assert(range <= expandMax, s"$variable can take on $range different valued. This is more than the maximum $expandMax!")
    val simp: smt.Expr => smt.Expr = if(simplify) { SMTSimplifier.simplify } else { e => e }
    val instances = (0 until range).map { ii =>
      simp(smt.Context.rewriteExpr(e, onExprExpand(_, variable, makeLit(ii, variable.typ)), mutable.Map.empty))
    }
    instances.reduce((a, b) => smt.OperatorApplication(glue, List(a, b)))
  }

  private def onExpr(e: smt.Expr): smt.Expr = e match {
    case smt.OperatorApplication(smt.ForallOp(List(v), _), List(e)) => expand(smt.ConjunctionOp, v, e)
    case smt.OperatorApplication(smt.ExistsOp(List(v), _), List(e)) => expand(smt.DisjunctionOp, v, e)
    case o @ smt.OperatorApplication(_ : smt.ForallOp, _) =>
      throw new NotImplementedError(s"Quantified expressions $o not supported")
    case o @ smt.OperatorApplication(_ : smt.ExistsOp, _) =>
      throw new NotImplementedError(s"Quantified expressions $o not supported")
    case other => other
  }

  def apply(e: smt.Expr): smt.Expr = smt.Context.rewriteExpr(e, onExpr, mutable.Map.empty)
}
