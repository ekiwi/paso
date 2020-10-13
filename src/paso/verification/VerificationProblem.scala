// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import maltese.smt

// Verification Graph
sealed trait VerificationNode {
  val next: Seq[VerificationNode]
  val methods: Set[String]
  def isFinal: Boolean = next.isEmpty
  def isBranchPoint: Boolean = next.length > 1
}

sealed trait IONode {
  val constraints: Seq[smt.BVExpr]
  val mappings: Seq[ArgumentEq]
  val hasGuardedMappings: Boolean = false
  lazy val constraintExpr: smt.BVExpr = smt.BVAnd(constraints)
  lazy val mappingExpr: smt.BVExpr = {
    val e = if(hasGuardedMappings) { mappings.map(_.toGuardedExpr()) } else { mappings.map(_.toExpr()) }
    smt.BVAnd(e)
  }
}

case class StepNode(next: Seq[InputNode], methods: Set[String], id: Int, isFork: Boolean) extends VerificationNode
case class InputNode(next: Seq[OutputNode], methods: Set[String], constraints: Seq[smt.BVExpr] = Seq(), mappings: Seq[ArgumentEq]= Seq()) extends VerificationNode with IONode
case class OutputNode(next: Seq[StepNode], methods: Set[String], constraints: Seq[smt.BVExpr] = Seq(), mappings: Seq[ArgumentEq]= Seq()) extends VerificationNode with IONode {
  override val hasGuardedMappings: Boolean = true
}

trait Assertion { def toExpr: smt.BVExpr }
case class BasicAssertion(guard: smt.BVExpr, pred: smt.BVExpr) extends Assertion {
  override def toExpr: smt.BVExpr = smt.BVImplies(guard, pred)
}
case class ForAllAssertion(variable: smt.BVSymbol, start: Int, end: Int, guard: smt.BVExpr, pred: smt.BVExpr) extends Assertion {
  override def toExpr: smt.BVExpr = {
    val max = 1 << variable.width
    val isFullRange = start == 0 && end == max
    val g = if(isFullRange) { guard } else {
      val lower = smt.BVComparison(smt.Compare.GreaterEqual, variable, smt.BVLiteral(start, variable.width), signed=false)
      val upper = smt.BVNot(smt.BVComparison(smt.Compare.Greater, variable, smt.BVLiteral(end-1, variable.width), signed=false))
      smt.BVAnd(guard, smt.BVAnd(lower, upper))
    }
    smt.BVForall(variable, smt.BVImplies(g, pred))
  }
}

case class Spec(untimed: UntimedModel, protocols: Map[String, StepNode])
case class Subspec(instance: String, ioSymbols: Seq[smt.BVSymbol], spec: Spec, binding: Option[String])
case class VerificationProblem(impl: smt.TransitionSystem, spec: Spec, subspecs: Seq[Subspec],
                               invariances: Seq[Assertion], mapping: Seq[Assertion])