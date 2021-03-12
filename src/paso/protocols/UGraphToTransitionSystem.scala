// Copyright 2020-2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>


package paso.protocols

import Chisel.log2Ceil
import maltese.mc
import maltese.smt
import paso.formal.PredicateEncoder
import firrtl.ir

/** Encodes a UGraph into a transition system.
 *  This requires that all edges are synchronous and transitions should be deterministic!
 */
class UGraphToTransitionSystem(g: UGraph, solver: GuardSolver) {

  import PredicateEncoder.not

  private val signalPrefix = g.name + ".automaton."
  private val stateBits = log2Ceil(g.nodes.length + 1)
  private val inState = g.nodes.indices.map(s => smt.BVSymbol(signalPrefix + s"stateIs$s", 1)).toArray
  private val invalidState = smt.BVSymbol(signalPrefix + "stateIsInvalid", 1)

  // global signals
  private val reset = smt.BVSymbol("reset", 1)
  private val notReset = smt.BVSymbol("notReset", 1)

  /** @param invert switches the role of asserts and assumes */
  def run(invert: Boolean): mc.TransitionSystem = {
    makeAuto(invert)
  }

  private def makeAuto(invert: Boolean): mc.TransitionSystem = {
    // define inState signals
    val state = smt.BVSymbol(signalPrefix + "state", stateBits)
    val maxState = smt.BVLiteral(g.nodes.length - 1, stateBits)
    val stateSignals = inState.zip(g.nodes.indices).map { case (sym, nid) =>
      mc.Signal(sym.name, smt.BVEqual(state, smt.BVLiteral(nid, stateBits)))
    } ++ Seq(
      mc.Signal(invalidState.name, smt.BVComparison(smt.Compare.Greater, state, maxState, signed=false)),
      mc.Signal(invalidState.name + "Check", not(smt.BVImplies(notReset, not(invalidState))), mc.IsBad)
    )

    // signal that can be used to constrain the state to be zero
    val stateIsZero = List(mc.Signal(signalPrefix + "initState", inState(0), mc.IsOutput))

    // encode actions
    val actions = getActionsInState(g.nodes)
    checkForUnsupportedActions(actions)
    val actionSignals = (
      encodePredicates(asssertPreds(actions), notReset, signalPrefix + "bad", assumeDontAssert = invert) ++
      encodePredicates(asssumePreds(actions), notReset, signalPrefix + "constraint", assumeDontAssert = !invert) ++
      encodeSignals(actions)
    )
    // TODO: mappings!

    // encode edges
    val stateState = encodeStateEdges(state, reset)

    val signals = stateSignals ++ stateIsZero ++ actionSignals
    mc.TransitionSystem("PasoAutomaton", List(), List(stateState), signals.toList)
  }


  private def checkForUnsupportedActions(as: Iterable[ActionInState]): Unit = {
    as.map(a => (a.a.a, a.a.info)).foreach { case (a, info) => a match {
      // supported actions:
      case _ : ASignal | _ : AAssume | _ : AAssert | _ : AMapping =>
      case a : ASet =>
        throw new RuntimeException(s"Unsupported action: $a${info.serialize}")
      case a : AUnSet =>
        throw new RuntimeException(s"Unsupported action: $a${info.serialize}")
      case AInputAssign(_) => // ignore for now
    }}
  }

  private def asssumePreds(a: Seq[ActionInState]): Seq[Pred] = {
    a.collect { case ActionInState(UAction(AAssume(cond), info, guard), in) =>
      Pred(smt.BVAnd(inState(in), guard), cond, info)
    }
  }
  private def asssertPreds(a: Seq[ActionInState]): Seq[Pred] = {
    a.collect { case ActionInState(UAction(AAssert(cond), info, guard), in) =>
      Pred(smt.BVAnd(inState(in), guard), cond, info)
    }
  }

  private case class Pred(guard: smt.BVExpr, pred: smt.BVExpr, info: ir.Info)
  private def encodePredicates(preds: Seq[Pred], notReset: smt.BVExpr, prefix: String, assumeDontAssert: Boolean): Iterable[mc.Signal] = {
    val negate = !assumeDontAssert
    val lbl = if(assumeDontAssert) mc.IsConstraint else mc.IsBad
    val notTriviallyTrue = preds.filterNot(_.pred == smt.True())
    val groups = notTriviallyTrue.groupBy(_.pred)
    groups.zipWithIndex.map { case ((_, ps), i) =>
      val guard = smt.BVOr(ps.map(_.guard))
      val expr = smt.BVImplies(smt.BVAnd(notReset, guard), ps.head.pred)
      val negatedExpr = if(negate) not(expr) else expr
      val simplifiedExpr = solver.simplify(negatedExpr)
      mc.Signal(s"${prefix}_$i", simplifiedExpr, lbl)
    }
  }

  private case class Edge(to: Int, guard: smt.BVExpr)
  private def encodeStateEdges(state: smt.BVSymbol, reset: smt.BVExpr): mc.State = {
    // we first collect all the edges
    val edges = g.nodes.zipWithIndex.flatMap { case (node, from) =>
      node.next.map { e => assert(e.isSync) ; Edge(e.to, smt.BVAnd(inState(from), e.guard)) }
    }

    // we want to compute the next state based on the current state and predicates
    val invalidState = smt.BVLiteral((BigInt(1) << stateBits) - 1, stateBits)
    val next = edges.groupBy(_.to).foldLeft[smt.BVExpr](invalidState) { case (other, (nextState, edges)) =>
      val guard = smt.BVOr(edges.map(_.guard))
      val simplified = solver.simplify(guard)
      smt.BVIte(simplified, smt.BVLiteral(nextState, stateBits), other)
    }
    val withReset = smt.BVIte(reset, smt.BVLiteral(0, stateBits), next)
    mc.State(state, init = None, next = Some(withReset))
  }

  private case class Signal(name: String, guard: smt.BVExpr, info: ir.Info)
  private def encodeSignals(actions: Seq[ActionInState]): Seq[mc.Signal] = {
    val signals = actions.collect{ case ActionInState(UAction(ASignal(name), info, guard), in) =>
      Signal(name, smt.BVAnd(inState(in), guard), info)
    }
    signals.groupBy(_.name).map { case (name, signals) =>
      val simplified = solver.simplify(smt.BVOr(signals.map(_.guard)))
      mc.Signal(name, simplified)
    }.toSeq
  }

  private case class ActionInState(a: UAction, in: Int)
  private def getActionsInState(n: Seq[UNode]): Seq[ActionInState] =
    n.zipWithIndex.flatMap { case (node, in) => node.actions.map(a => ActionInState(a, in) ) }
}