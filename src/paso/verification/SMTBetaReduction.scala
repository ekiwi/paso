// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import paso.chisel.SMTSimplifier
import uclid.smt

import scala.collection.mutable

/**
 * eliminates all smt.FunctionApplication by inlining their definition
* */
case class SMTBetaReduction(foos: Seq[smt.DefineFun]) {
  private val symToFoo = foos.map(f => f.id -> f).toMap
  type Subs = Map[smt.Symbol, smt.Expr]

  private def onExpr(e: smt.Expr, subs: Subs): smt.Expr = e match {
    case s: smt.Symbol => subs.getOrElse(s, s)
    case smt.FunctionApplication(e, args) =>
      assert(e.isInstanceOf[smt.Symbol])
      assert(symToFoo.contains(e.asInstanceOf[smt.Symbol]), s"Unknown function $e called with arguments $args")
      val foo = symToFoo(e.asInstanceOf[smt.Symbol])
      // calculate new substitutions
      val resolvedArgs = args.map(onExpr(_, subs))
      assert(resolvedArgs.length == foo.args.length)
      val newSubs = foo.args.zip(resolvedArgs).toMap
      onExpr(foo.e, subs ++ newSubs)
    case other => other
  }

  def apply(e: smt.Expr): smt.Expr = smt.Context.rewriteExpr(e, onExpr(_, Map()), mutable.Map.empty)
}
