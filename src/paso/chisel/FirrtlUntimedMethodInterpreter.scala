// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import firrtl.annotations.Annotation
import firrtl.ir
import paso.{GuardAnnotation, MethodIOAnnotation}
import uclid.smt

class FirrtlUntimedMethodInterpreter(circuit: ir.Circuit, annos: Seq[Annotation]) extends PasoFirrtlInterpreter(circuit, annos) {
  private val ios = annos.collect { case MethodIOAnnotation(target, isInput) => target.ref -> isInput }.toMap
  private val guards = annos.collect { case GuardAnnotation(target) => target.ref }.toSet
  assert(guards.size == 1, "Exactly one guard expected")
  private var guard: smt.Expr = smt.BooleanLit(true)

  override def onAssign(name: String, expr: smt.Expr): Unit = {
    val simp_expr = SMTSimplifier.simplify(expr)
    if(guards.contains(name)) { guard = simp_expr }
    println(s"$name <= $simp_expr")
  }
}