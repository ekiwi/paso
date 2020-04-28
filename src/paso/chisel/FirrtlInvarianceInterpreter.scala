// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import chisel3.util.log2Ceil
import firrtl.annotations.Annotation
import firrtl.ir
import firrtl.ir.Type
import paso.{ForallEndAnnotation, ForallStartAnnotation, MemEqualAnnotation, MemToVecAnnotation}
import paso.verification.{Assertion, BasicAssertion, ForAllAssertion, substituteSmt}
import uclid.smt

import scala.collection.mutable

class FirrtlInvarianceInterpreter(circuit: ir.Circuit, annos: Seq[Annotation]) extends PasoFirrtlInterpreter(circuit, annos) {
  // substitute memory equality and Vec as Mem wires
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

  // collect assertions
  val asserts = mutable.ArrayBuffer[Assertion]()

  // track forall scope
  private val forallStart = annos.collect{ case ForallStartAnnotation(target, start, end) => target.ref -> (start, end) }.toMap
  private val forallEnd = annos.collect{ case ForallEndAnnotation(target) => target.ref }.toSet
  private case class ForallScope(variable: smt.Symbol, start: Int, end: Int)
  private var forallScope: Option[ForallScope] = None
  override def defWire(name: String, tpe: Type): Unit = {
    super.defWire(name, tpe)
    forallStart.get(name) match {
      case Some((start, end)) =>
        assert(forallScope.isEmpty, "Currently nested forall/foreach blocks are not supported!")
        assert(cond_stack.isEmpty, "Currently only top level forall/foreach blocks are supported (nesting in a when block is not implemented).")
        val variable = smt.Symbol(name, wires(name))
        forallScope = Some(ForallScope(variable, start, end))
      case None =>
        if(forallEnd.contains(name)) {
          assert(forallScope.nonEmpty, "Trying to exit forall block failed: no active forall block!")
          forallScope = None
        }
    }
  }

  private def simp(e: smt.Expr): smt.Expr = SMTSimplifier.simplify(e)

  def makeAsserts(guard: smt.Expr, pred: smt.Expr): Seq[Assertion] = pred match {
    case smt.OperatorApplication(smt.ConjunctionOp, List(a,b)) => makeAsserts(guard, a) ++ makeAsserts(guard, b)
    case other => Seq(
      forallScope match {
        case Some(ForallScope(variable, start, end)) => ForAllAssertion(variable, start, end, simp(guard), simp(other))
        case None => BasicAssertion(simp(guard), simp(other))
      }
    )
  }

  override def onAssert(expr: Value): Unit = {
    //val e = substituteSmt(mergeArrayEquality(expr.get), vecAsMem)
    val e = substituteSmt(expr.get, subs)
    asserts ++= makeAsserts(pathCondition, e)
  }
}
