// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import uclid.smt

case class MethodSemantics(guard: smt.Expr, updates: Map[String, smt.Expr], outputs: Map[String, smt.Expr], inputs: Map[String, smt.Type])
case class UntimedModel(name: String, state: Map[String, smt.Type], methods: Map[String, MethodSemantics])
