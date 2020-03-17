// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import chisel3.util.log2Ceil
import paso.chisel.SMTSimplifier
import uclid.smt
import uclid.smt.SymbolicTransitionSystem

import scala.collection.mutable

case class BoundedCheck()

case class CheckStep(ii: Int, assertions: Seq[smt.Expr] = Seq(), assumptions: Seq[smt.Expr] = Seq())

class BoundedCheckBuilder(base: smt.SymbolicTransitionSystem) {
  require(base.constraints.isEmpty)
  require(base.bad.isEmpty)
  require(base.fair.isEmpty)
  private val sys = base
  private val steps = mutable.ArrayBuffer[CheckStep]()
  private val sysSymbols =
    (sys.outputs.map{ case (name, expr) => smt.Symbol(name, expr.typ) } ++ sys.inputs ++ sys.states.map(_.sym))
      .map(s => s.id -> s.typ).toMap
  private val defines = mutable.HashMap[String, smt.Expr]()

  private def extendTo(ii: Int): Unit = {
    while(steps.length <= ii) {
      steps.append(CheckStep(steps.length))
    }
  }

  def assertAt(ii : Int, expr: smt.Expr): Unit = {
    extendTo(ii)
    val step = steps(ii)
    steps(ii) = step.copy(assertions = step.assertions ++ Seq(expr))
    //println(s"assert @ $ii: ${SMTSimplifier.simplify(expr)}")
  }

  def assumeAt(ii : Int, expr: smt.Expr): Unit = {
    extendTo(ii)
    val step = steps(ii)
    steps(ii) = step.copy(assumptions = step.assumptions ++ Seq(expr))
    //println(s"assume @ $ii: ${SMTSimplifier.simplify(expr)}")
  }

  def define(name: smt.Symbol, expr: smt.Expr): Unit = {
    require(name.typ == expr.typ, s"Type mismatch: ${name.typ} != ${expr.typ}")
    require(!sysSymbols.contains(name.id), s"Name collision with symbol in Transition System: ${name.id} : ${sysSymbols(name.id)}")
    require(!defines.contains(name.id), s"Name collision with previously defined symbol: ${name.id} : ${defines(name.id).typ} := ${defines(name.id)}")
    defines(name.id) = expr
  }

  def getSystems: Seq[smt.SymbolicTransitionSystem] = {
    val allExpr = steps.flatMap(s => s.assumptions ++ s.assertions) ++ defines.values
    val allSymbols : Set[smt.Symbol] = allExpr.map(smt.Context.findSymbols).reduce((a,b) => a | b)

    // check that there are no aliases with a different type
    allSymbols.foreach { sym =>
      assert(sysSymbols.get(sym.id).forall(sym.typ == _),
        s"Type mismatch with symbol in Transition System: ${sym.id} : ${sysSymbols(sym.id)} != ${sym.typ}")
      assert(defines.get(sym.id).forall(sym.typ == _.typ),
        s"Type mismatch with defined symbol: ${sym.id} : ${defines(sym.id).typ} != ${sym.typ}")
    }

    // all  unknown symbols are assumed to be symbolic constants
    val knownSymbols : Set[smt.Symbol] = (sysSymbols.map(i => smt.Symbol(i._1, i._2)) ++ defines.map(i => smt.Symbol(i._1, i._2.typ))).toSet
    val symConsts : Seq[smt.Symbol] = (allSymbols diff knownSymbols).toSeq

    // emulate defines and symbolic constants with states
    val constStates = symConsts.map(s => smt.State(s, next=Some(s)))
    val defineStates = defines.map{ case (name, expr) =>
      val s = smt.Symbol(name, expr.typ)
      smt.State(s, init=Some(expr), next=Some(s))
    }

    // emulate steps with counter
    val counterBits = log2Ceil(steps.length)
    val counter = smt.Symbol("__counter", smt.BitVectorType(counterBits))
    val counterNext = smt.OperatorApplication(smt.BVAddOp(counterBits), List(counter, smt.BitVectorLit(1, counterBits)))
    val counterState = smt.State(counter, init=Some(smt.BitVectorLit(0, counterBits)), next=Some(counterNext))
    def in_step(ii: Int, expr: smt.Expr): smt.Expr = smt.OperatorApplication(smt.ImplicationOp, List(
      smt.OperatorApplication(smt.EqualityOp, List(counter, smt.BitVectorLit(ii, counterBits))), expr
    ))

    // translate step assumptions/assertions into global constraints/bad states
    val constraints = steps.flatMap{ s => s.assumptions.map(in_step(s.ii, _))}
    val badStates = steps.flatMap{ s => s.assertions.map(a => smt.OperatorApplication(smt.NegationOp, List(in_step(s.ii, a)))) }

    // create a transition system containing the checks, it will be serialized right after the original system
    val states = constStates ++ defineStates ++ Seq(counterState)
    val check = SymbolicTransitionSystem(name= None, inputs = Seq(), states = states, constraints = constraints, bad = badStates)

    Seq(sys, check)
  }
}

object BoundedCheckBuilder {

}