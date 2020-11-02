// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.smt

private sealed trait SMTCommand
private case class Comment(msg: String) extends SMTCommand
private case class DefineFunction(name: String, args: Seq[SMTSymbol], e: SMTExpr) extends SMTCommand
private case class DeclareFunction(sym: SMTSymbol, args: Seq[SMTType]) extends SMTCommand
private case class DeclareUninterpretedSort(name: String) extends SMTCommand
