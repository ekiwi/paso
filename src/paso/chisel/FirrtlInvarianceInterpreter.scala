// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import firrtl.annotations.Annotation
import firrtl.ir
import uclid.smt

import scala.collection.mutable

case class Assertion(guard: smt.Expr, pred: smt.Expr)

class FirrtlInvarianceInterpreter(circuit: ir.Circuit, annos: Seq[Annotation]) extends PasoFirrtlInterpreter(circuit, annos) {
  val asserts = mutable.ArrayBuffer[Assertion]()
  override def onAssert(expr: smt.Expr): Unit = {
    asserts.append(Assertion(pathCondition, expr))
  }
}
