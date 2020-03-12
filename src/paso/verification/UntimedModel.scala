// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import uclid.smt

case class NamedExpr(sym: smt.Symbol, expr: smt.Expr)
case class MethodSemantics(guard: smt.Expr, updates: Seq[NamedExpr], outputs: Seq[NamedExpr], inputs: Seq[smt.Expr])
case class UntimedModel(name: String, state: Seq[smt.Symbol], methods: Map[String, MethodSemantics], init: Seq[NamedExpr])
