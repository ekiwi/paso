// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import chisel3.util.log2Ceil
import firrtl.annotations.Annotation
import firrtl.ir
import paso.MemToVecAnnotation
import paso.verification.{Assertion, substituteSmt}
import uclid.smt

import scala.collection.mutable

class FirrtlInvarianceInterpreter(circuit: ir.Circuit, annos: Seq[Annotation]) extends PasoFirrtlInterpreter(circuit, annos) {
  private val vecAsMem: Map[smt.Expr, smt.Expr] = annos.collect {
    case MemToVecAnnotation(vec, mem, depth, width) =>
      val typ = smt.ArrayType(List(smt.BitVectorType(log2Ceil(depth))), smt.BitVectorType(width))
      smt.Symbol(vec.ref, typ) -> smt.Symbol(mem.module + "." + mem.ref, typ)
  }.toMap
  val asserts = mutable.ArrayBuffer[Assertion]()

  private def simp(e: smt.Expr): smt.Expr = SMTSimplifier.simplify(e)

  def makeAsserts(guard: smt.Expr, pred: smt.Expr): Seq[Assertion] = pred match {
    case smt.OperatorApplication(smt.ConjunctionOp, List(a,b)) => makeAsserts(guard, a) ++ makeAsserts(guard, b)
    case other => Seq(Assertion(simp(guard), simp(other)))
  }

  override def onAssert(expr: smt.Expr): Unit = {
    asserts ++= makeAsserts(pathCondition, substituteSmt(expr, vecAsMem))
  }
}
