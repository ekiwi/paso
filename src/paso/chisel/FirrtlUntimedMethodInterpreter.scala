// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import firrtl.annotations.Annotation
import firrtl.ir
import firrtl.ir.Reference
import paso.{GuardAnnotation, MethodIOAnnotation}
import uclid.smt

import scala.collection.mutable

case class MethodSemantics(guard: smt.Expr, updates: Map[String, smt.Expr], outputs: Map[String, smt.Expr], inputs: Map[String, smt.Type])

class FirrtlUntimedMethodInterpreter(circuit: ir.Circuit, annos: Seq[Annotation]) extends PasoFirrtlInterpreter(circuit, annos) {
  private val methodInputs = annos.collect { case MethodIOAnnotation(target, true) => target.ref }.toSet
  private val methodOutputs = annos.collect { case MethodIOAnnotation(target, false) => target.ref }.toSet
  private val guards = annos.collect { case GuardAnnotation(target) => target.ref }.toSet
  assert(guards.size == 1, "Exactly one guard expected")
  private var guard: smt.Expr = smt.BooleanLit(true)
  private val stateUpdates = mutable.HashMap[String, smt.Expr]()
  private val outputExpr = mutable.HashMap[String, smt.Expr]()

  def getSemantics: MethodSemantics = {
    // check that we have assignments for all outputs
    methodOutputs.foreach { o =>
      assert(outputExpr.contains(o), s"Output $o was never assigned!")
    }
    // if a state was not updated, it stays the same
    val updates = (regs ++ mems).map { case (name, tpe) =>
      name -> stateUpdates.getOrElse(name, smt.Symbol(name, tpe))
    }.toMap
    // find input types
    val ins = methodInputs.map { ii => ii -> wires(ii)}.toMap
    MethodSemantics(guard=guard, updates = updates, outputs = outputExpr.toMap, inputs = ins)
  }

  override def onAssign(name: String, expr: smt.Expr): Unit = {
    val simp_expr = SMTSimplifier.simplify(expr)
    if(guards.contains(name)) {
      guard = simp_expr
    } else if(regs.contains(name) || mems.contains(name)) {
      assert(!stateUpdates.contains(name), "Currently only a single state assignment is allowed")
      assert(pathCondition == smt.BooleanLit(true), "Currently conditional updates are not supported")
      stateUpdates(name) = simp_expr
    } else if(methodOutputs.contains(name)) {
      assert(!outputExpr.contains(name), "Currently only a single output assignment is allowed")
      assert(pathCondition == smt.BooleanLit(true), "Currently conditional updates are not supported")
      outputExpr(name) = simp_expr
    }
    //println(s"$name <= $simp_expr")
  }
}