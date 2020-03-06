// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import uclid.smt
import uclid.smt.SolverResult

trait CallCount {
  def callCount: Int
}

class YicesInterface extends smt.SMTLIB2Interface(List("yices-smt2", "--incremental")) with CallCount {
  writeCommand("(set-logic QF_AUFBV)")

  override def getModel() : Option[smt.Model] = {
    return None
    // TODO
    uclid.Utils.assert(solverProcess.isAlive(), "Solver process is not alive! Cannot retrieve model.")
    writeCommand("(get-model)")
    readResponse() match {
      case Some(strModel) =>
        Some(new smt.SMTLIB2Model(strModel.stripLineEnd))
      case None =>
        throw new uclid.Utils.AssertionError("Unexpected EOF result from SMT solver.")
    }
  }

  private var pCallCount = 0
  override def check(): SolverResult = {
    pCallCount += 1
    super.check()
  }

  def callCount: Int = pCallCount
}