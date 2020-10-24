// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import Chisel.log2Ceil
import maltese.mc.{IsBad, ModelCheckFail, ModelCheckSuccess, Signal, State, TransitionSystem}
import maltese.{mc, smt}
import maltese.smt.solvers.{Solver, Yices2}
import paso.protocols.{PasoAutomatonEncoder, ProtocolGraph}
import paso.untimed

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

case class UntimedModel(sys: mc.TransitionSystem, methods: Seq[untimed.MethodInfo]) {
  def name: String = sys.name
  def addPrefix(prefix: String): UntimedModel = copy(sys = sys.copy(name = prefix + name))
}
case class Spec(untimed: UntimedModel, protocols: Seq[ProtocolGraph])
case class Subspec(instance: String, ioSymbols: Seq[smt.BVSymbol], spec: Spec, binding: Option[String])
case class VerificationProblem(impl: TransitionSystem, spec: Spec, subspecs: Seq[Subspec], invariants: TransitionSystem)

object VerificationProblem {
  def verify(problem: VerificationProblem, opt: paso.ProofOptions): Unit = {
    // check to see if the mappings contain quantifiers
    //val quantifierFree = !(problem.mapping ++ problem.invariances).exists(_.isInstanceOf[ForAllAssertion])
    //assert(quantifierFree, "TODO: expand quantifiers when needed (for btor2 and yices)")
    val checker =  new mc.BtormcModelChecker()

    // turn the protocol and untimed model into a paso automaton
    val solver = Yices2()
    val spec = makePasoAutomaton(problem.spec.untimed, problem.spec.protocols, solver)

    // connect the implementation to the global reset
    val impl = connectToReset(problem.impl)

    // encode invariants
    val startState = smt.BVSymbol(spec.name + ".automaton.startState", 1)
    val invariants = encodeInvariants(startState, problem.invariants)

    // for the base case we combine everything together with a reset
    val baseCase = List(generateInitialReset(), impl, spec, invariants)
    val baseCaseSys = mc.TransitionSystem.combine("BaseCase", baseCase)

    // generate base case btor
    println(baseCaseSys.serialize)
    val res = checker.check(baseCaseSys, kMax = 1, fileName = Some("basecase.btor2"))
    res match {
      case ModelCheckFail(witness) =>
        println("Base case fails!")
      case ModelCheckSuccess() =>
        println("Base case works!")
    }

    // check all our simplifications
    assert(!opt.checkSimplifications, "Cannot check simplifications! (not implement)")
  }

  def bmc(problem: VerificationProblem, solver: paso.SolverName, kMax: Int): Unit = {
    throw new NotImplementedError("TODO: implement BMC")
  }

  private def makePasoAutomaton(untimed: UntimedModel, protocols: Iterable[ProtocolGraph], solver: Solver): TransitionSystem = {
    val automaton = new PasoAutomatonEncoder(untimed, protocols, solver).run()
    new PasoAutomatonToTransitionSystem(automaton).run()
  }

  private def generateInitialReset(length: Int = 1): TransitionSystem = {
    assert(length >= 1)
    val counterBits = List(log2Ceil(length), 1).max
    val counterMax = smt.BVLiteral((BigInt(1) << counterBits) - 1, counterBits)
    val counter = smt.BVSymbol("resetCounter", counterBits)
    val counterNext = smt.BVIte(smt.BVEqual(counter, counterMax), counter, smt.BVOp(smt.Op.Add, counter, smt.BVLiteral(1, counterBits)))
    val state = State(counter, init=Some(smt.BVLiteral(0, counterBits)), next=Some(counterNext))
    val reset = Signal("reset", smt.BVComparison(smt.Compare.GreaterEqual, counter, smt.BVLiteral(length, counterBits), signed = false))
    val notReset = Signal("notReset", smt.BVNot(smt.BVSymbol("reset", 1)))
    mc.TransitionSystem("reset", List(), List(state), List(reset, notReset))
  }

  private def generateDisabledReset(): TransitionSystem = {
    val reset = mc.Signal("reset", smt.BVLiteral(0, 1))
    val notReset = mc.Signal("notReset", smt.BVLiteral(1, 1))
    mc.TransitionSystem("reset", List(), List(), List(reset, notReset))
  }

  private def connectToReset(sys: TransitionSystem): TransitionSystem = connect(sys, Map(sys.name + ".reset" ->  reset))

  private def encodeInvariants(start: smt.BVExpr, invariants: TransitionSystem): TransitionSystem = {
    val sys = connect(invariants, Map(
      invariants.name + ".reset" -> reset,
      invariants.name + ".enabled" -> smt.BVAnd(smt.BVNot(reset), start)
    ))
    assert(sys.inputs.isEmpty, s"Unexpected inputs: ${sys.inputs.mkString(", ")}")
    sys
  }

  private def connect(sys: TransitionSystem, cons: Map[String, smt.BVExpr]): TransitionSystem = {
    // ensure that the ports exists
    cons.foreach(i => assert(sys.inputs.exists(_.name == i._1), s"Cannot connect to non-existing port ${i._1}"))
    // filter out inputs
    val inputs = sys.inputs.filterNot(i => cons.contains(i.name))
    val connections = cons.map(c => mc.Signal(c._1, c._2)).toList
    sys.copy(inputs = inputs, signals = connections ++ sys.signals)
  }

  private val reset = smt.BVSymbol("reset", 1)
}
