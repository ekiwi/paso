// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import paso.chisel.SMTSimplifier
import uclid.smt

import scala.collection.mutable

case class BoundedCheck()

case class CheckStep(ii: Int, assertions: Seq[smt.Expr] = Seq(), assumptions: Seq[smt.Expr] = Seq())

class BoundedCheckBuilder(base: smt.SymbolicTransitionSystem) {
  private var sys = base
  private val steps = mutable.ArrayBuffer[CheckStep]()

  private def extendTo(ii: Int): Unit = {
    while(steps.length <= ii) {
      steps.append(CheckStep(steps.length))
    }
  }

  def assertAt(ii : Int, expr: smt.Expr): Unit = {
    extendTo(ii)
    val step = steps(ii)
    steps(ii) = step.copy(assertions = step.assertions ++ Seq(expr))
    println(s"assert @ $ii: ${SMTSimplifier.simplify(expr)}")
  }

  def assumeAt(ii : Int, expr: smt.Expr): Unit = {
    extendTo(ii)
    val step = steps(ii)
    steps(ii) = step.copy(assumptions = step.assumptions ++ Seq(expr))

    println(s"assume @ $ii: ${SMTSimplifier.simplify(expr)}")

  }

  def getBoundedCheck: BoundedCheck = BoundedCheck()
}