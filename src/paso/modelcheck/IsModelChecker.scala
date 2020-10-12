// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.modelcheck

import maltese.smt

trait ModelCheckResult {
  def isFail: Boolean
  def isSuccess: Boolean = !isFail
}
case class ModelCheckSuccess() extends ModelCheckResult { override def isFail: Boolean = false }
case class ModelCheckFail(witness: Witness) extends ModelCheckResult { override def isFail: Boolean = true }

trait IsModelChecker {
  val name: String
  val supportsUF: Boolean = false
  val supportsQuantifiers: Boolean = false
  def check(sys: TransitionSystem, kMax: Int = -1, fileName: Option[String] = None, defined: Seq[DefineFun] = Seq(), uninterpreted: Seq[Symbol] = Seq()): ModelCheckResult
}