// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import uclid.smt

case class NamedExpr(sym: smt.Symbol, expr: smt.Expr)
case class NamedGuardedExpr(sym: smt.Symbol, expr: smt.Expr, guard: smt.Expr)
case class MethodSemantics(guard: smt.Expr, updates: Seq[NamedExpr], outputs: Seq[NamedGuardedExpr], inputs: Seq[smt.Symbol])
case class UntimedModel(name: String, state: Seq[smt.State], methods: Map[String, MethodSemantics])
