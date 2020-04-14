// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import chisel3.util.log2Ceil
import firrtl.annotations.Annotation
import firrtl.ir
import paso.{MemEqualAnnotation, MemToVecAnnotation}
import paso.verification.{Assertion, substituteSmt}
import uclid.smt

import scala.collection.mutable

class FirrtlInvarianceInterpreter(circuit: ir.Circuit, annos: Seq[Annotation]) extends PasoFirrtlInterpreter(circuit, annos) {
  private def memTyp(depth: BigInt, width: Int): smt.Type = {
    smt.ArrayType(List(smt.BitVectorType(log2Ceil(depth))), smt.BitVectorType(width))
  }
  private val vecAsMem: Map[smt.Expr, smt.Expr] = annos.collect {
    case MemToVecAnnotation(vec, mem, depth, width) =>
      val typ = memTyp(depth, width)
      smt.Symbol(vec.ref, typ) -> smt.Symbol(mem.module + "." + mem.ref, typ)
  }.toMap
  private val memEqual: Map[smt.Expr, smt.Expr] = annos.collect { case MemEqualAnnotation(target, mem0, mem1, depth, width) =>
    val typ = memTyp(depth, width)
    smt.Symbol(target.ref, smt.BoolType) -> eq(smt.Symbol(mem0.module + "." + mem0.ref, typ), smt.Symbol(mem1.module + "." + mem1.ref, typ))
  }.toMap
  private val subs = vecAsMem ++ memEqual
  val asserts = mutable.ArrayBuffer[Assertion]()

  private def simp(e: smt.Expr): smt.Expr = SMTSimplifier.simplify(e)

  def makeAsserts(guard: smt.Expr, pred: smt.Expr): Seq[Assertion] = pred match {
    case smt.OperatorApplication(smt.ConjunctionOp, List(a,b)) => makeAsserts(guard, a) ++ makeAsserts(guard, b)
    case other => Seq(Assertion(simp(guard), simp(other)))
  }

  override def onAssert(expr: Value): Unit = {
    //val e = substituteSmt(mergeArrayEquality(expr.get), vecAsMem)
    val e = substituteSmt(expr.get, subs)
    asserts ++= makeAsserts(pathCondition, e)
  }

  override def onIsInvalid(expr: Value): Unit = {} // ignore invalids
}
