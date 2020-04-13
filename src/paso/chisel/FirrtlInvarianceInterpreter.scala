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

  /* this deals with the fact that Chisel expands comparisons between Vec into element wise comparisons */
  // old dead code that was used when arrays were expanded to vectors
  private def mergeArrayEquality(e: smt.Expr): smt.Expr = {
    val clauses = conjunctionToSeq(e)
    val arrayEq = clauses.map(parseArrayEq)
    val allArrayEq = arrayEq.forall(_.nonEmpty)
    if(allArrayEq) {
      val (a0, a1, _) = arrayEq.head.get
      assert(a0.typ == a1.typ)
      val depth = getArrayDepth(a0.typ)
      if(arrayEq.size == depth) {
        val complete = arrayEq.zipWithIndex.forall {
          case (Some((b0, b1, addr)), i) => b0 == a0 && b1 == a1 && addr.toInt == i
        }
        if (complete) {
          smt.OperatorApplication(smt.EqualityOp, List(a0, a1))
        } else { e }
      } else { e }
    } else { e }
  }
  private def parseArrayEq(e: smt.Expr): Option[(smt.Symbol, smt.Symbol, BigInt)] = e match {
    case smt.OperatorApplication(smt.EqualityOp, List(
      smt.ArraySelectOperation(a0: smt.Symbol, List(smt.BitVectorLit(i0, _))),
      smt.ArraySelectOperation(a1: smt.Symbol, List(smt.BitVectorLit(i1, _))))) if i0 == i1 => Some((a0, a1, i0))
    case _ => None
  }
  private def conjunctionToSeq(e: smt.Expr): Seq[smt.Expr] = e match {
    case smt.OperatorApplication(smt.ConjunctionOp, List(a,b)) => conjunctionToSeq(a) ++ conjunctionToSeq(b)
    case other => Seq(other)
  }
  private def getArrayDepth(typ: smt.Type): BigInt = typ match {
    case smt.ArrayType(List(smt.BitVectorType(w)), _) => BigInt(1) << w
  }
}
