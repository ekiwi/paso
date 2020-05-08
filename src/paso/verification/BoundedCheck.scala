// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import chisel3.util.log2Ceil
import paso.chisel.{SMTHelper, SMTSimplifier}
import uclid.smt

import scala.collection.mutable

case class BoundedCheck()

case class CheckStep(ii: Int, assertions: Seq[smt.Expr] = Seq(), assumptions: Seq[smt.Expr] = Seq())

class BoundedCheckBuilder(val sys: smt.TransitionSystem, val debugPrint: Boolean = false) {
  require(sys.constraints.isEmpty)
  require(sys.bad.isEmpty)
  require(sys.fair.isEmpty)
  private val constraints = mutable.ArrayBuffer[smt.Expr]()
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
    if(debugPrint) {
      val simpl = SMTSimplifier.simplify(expr)
      if(simpl != SMTHelper.tru) println(s"assert @ $ii: $simpl")
    }
  }

  def assumeAt(ii : Int, expr: smt.Expr): Unit = {
    extendTo(ii)
    val step = steps(ii)
    steps(ii) = step.copy(assumptions = step.assumptions ++ Seq(expr))
    // check for trivially false assumptions
    val simpl = SMTSimplifier.simplify(expr)
    assert(simpl != SMTHelper.fals, s"Assuming false! https://xkcd.com/704/ ($expr)")
    if(debugPrint) {
      if(simpl != SMTHelper.tru) println(s"assume @ $ii: $simpl")
    }
  }

  def assume(expr: smt.Expr): Unit = {
    constraints.append(expr)
    if(debugPrint) println(s"assume: $expr")
  }

  // TODO: add support for functions with arguments instead of just defines (this will be used for the new method semantics model)
  def define(name: smt.Symbol, expr: smt.Expr): Unit = {
    require(name.typ == expr.typ, s"Type mismatch: ${name.typ} != ${expr.typ}")
    require(!sysSymbols.contains(name.id), s"Name collision with symbol in Transition System: ${name.id} : ${sysSymbols(name.id)}")
    require(!defines.contains(name.id), s"Name collision with previously defined symbol: ${name.id} : ${defines(name.id).typ} := ${defines(name.id)}")
    defines(name.id) = expr
    if(debugPrint) println(s"define: $name := $expr")
  }

  def getCombinedSystem: smt.TransitionSystem = {
    val allExpr = steps.flatMap(s => s.assumptions ++ s.assertions) ++ defines.values
    val allSymbols : Set[smt.Symbol] = allExpr.map(SMTFindFreeSymbols(_)).reduce((a,b) => a | b)

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
    // TODO: inline defines (at least at an option to)
    val defineStates = defines.map{ case (name, expr) =>
      val s = smt.Symbol(name, expr.typ)
      smt.State(s, init=Some(expr), next=Some(s))
    }

    // emulate steps with counter
    val counterBits = if(steps.length > 1) log2Ceil(steps.length) else 1
    val counter = smt.Symbol("__counter", smt.BitVectorType(counterBits))
    val counterNext = smt.OperatorApplication(smt.BVAddOp(counterBits), List(counter, smt.BitVectorLit(1, counterBits)))
    val counterState = smt.State(counter, init=Some(smt.BitVectorLit(0, counterBits)), next=Some(counterNext))
    def in_step(ii: Int, expr: smt.Expr): smt.Expr = smt.OperatorApplication(smt.ImplicationOp, List(
      smt.OperatorApplication(smt.EqualityOp, List(counter, smt.BitVectorLit(ii, counterBits))), expr
    ))

    // translate step assumptions/assertions into global constraints/bad states
    val consts = steps.flatMap{ s => s.assumptions.map(in_step(s.ii, _))} ++ constraints
    val badStates = steps.flatMap{ s => s.assertions.map(a => smt.OperatorApplication(smt.NegationOp, List(in_step(s.ii, a)))) }

    // merge everything into a combined transition system
    val states = sys.states ++ constStates ++ defineStates ++ Seq(counterState)
    val combined = sys.copy(states = states, constraints = sys.constraints ++ consts, bad = sys.bad ++ badStates)

    combined.sortStatesByInitDependencies()
  }

  def getK: Int = steps.length
}

object BoundedCheckBuilder {

}