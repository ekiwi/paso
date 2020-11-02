// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.smt.solvers

import maltese.smt
import maltese.smt.solvers.Solver.Logic

class Yices2SMTLib extends SMTLibSolver(List("yices-smt2", "--incremental")) {
  override def name = "yices2-smtlib"
  override def supportsConstArrays = false
  override def supportsUninterpretedFunctions = true
}

class CVC4SMTLib extends SMTLibSolver(List("cvc4", "--incremental", "--produce-models", "--lang", "smt2")) {
  override def name = "cvc4-smtlib"
  override def supportsConstArrays = true
  override def supportsUninterpretedFunctions = true
}

class Z3SMTLib extends SMTLibSolver(List("z3", "-in")) {
  override def name = "z3-smtlib"
  override def supportsConstArrays = true
  override def supportsUninterpretedFunctions = true
}


/** provides basic facilities to interact with any SMT solver that supports a SMTLib base textual interface */
abstract class SMTLibSolver(cmd: List[String]) extends Solver {



  override def push(): Unit = ???
  override def pop(): Unit = ???
  override def assert(expr: smt.BVExpr): Unit = ???
  override def queryModel(e: smt.BVSymbol) = ???
  override def getValue(e: smt.BVExpr) = ???
  override def runCommand(cmd: SMTCommand): Unit = ???

  /** releases all native resources */
  override def close(): Unit = ???
  override protected def doSetLogic(logic: Logic): Unit = ???
  override protected def doCheck(produceModel: Boolean) = ???
}


