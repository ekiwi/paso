// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import Chisel.log2Ceil
import maltese.smt
import paso.protocols._
import paso.untimed.MethodInfo

/** Turns the PasoAutomaton into a TransitionSystem which can then be combined with the Design Under Verification
 *  for bounded model checking or inductive proofs.
 */
class PasoAutomatonToTransitionSystem(auto: PasoAutomaton) {
  private val signalPrefix = auto.untimed.name + ".automaton."
  private val stateBits = log2Ceil(auto.states.length + 1)
  private val inState = auto.states.map(s => smt.BVSymbol(signalPrefix + s"state_is_${s.id}", 1)).toArray
  private val invalidState = smt.BVSymbol(signalPrefix + "state_is_invalid", 1)

  def run(): smt.TransitionSystem = {
    // TODO: deal with multiple copies of the same protocol/transaction

    // connect inState signals
    val state = smt.BVSymbol(signalPrefix + "state", stateBits)
    val maxState = smt.BVLiteral(auto.states.length - 1, stateBits)
    val stateSignals = inState.zip(auto.states).map { case (sym, st) =>
      smt.Signal(sym.name, smt.BVEqual(state, smt.BVLiteral(st.id, stateBits)))
    } :+ smt.Signal(invalidState.name, smt.BVComparison(smt.Compare.Greater, state, maxState, signed=false))


    // connect method enabled inputs and arguments
    val methodInputs = connectMethodEnabled(auto.commits, auto.untimed.methods) ++
      connectMethodArgs(auto.mappings, auto.untimed.methods)

    // encode assertions and assumptions
    val assertions = compactEncodePredicates(auto.assertions, signalPrefix + "bad", smt.IsBad, invert=true)
    val assumptions = compactEncodePredicates(auto.assumptions, signalPrefix + "constraint", smt.IsConstraint, invert=false)

    // protocol states are the previous argument trackers and the FSM state
    val states = Seq(encodeStateEdges(state, auto.edges)) ++ prevMethodArgs(auto.untimed.methods)

    // combine untimed model and paso automaton into a single transition system
    val allSignals = stateSignals ++ methodInputs ++ auto.untimed.sys.signals ++ assumptions ++ assertions
    val allStates = states ++ auto.untimed.sys.states
    // while these should always be optimized away, we keep the RANDOM... inputs for now
    val combinedInputs = auto.untimed.sys.inputs.filter(_.name.startsWith("RANDOM"))
    val combined = smt.TransitionSystem(auto.untimed.sys.name, combinedInputs, allStates.toList, allSignals.toList)

    // we need to do a topological sort on the combined systems since not all signals might be in the correct order
    TopologicalSort.run(combined)
  }

  private def connectMethodEnabled(commits: Seq[PasoGuardedCommit], methods: Iterable[MethodInfo]): Iterable[smt.Signal] = {
    val methodToCommits = commits.groupBy(_.commit.name)
    methods.map { m =>
      val signalName = m.fullIoName + "_enabled"
      val commits = methodToCommits.getOrElse(signalName, List())
      val en = if(commits.isEmpty) smt.False() else smt.BVOr(commits.map(c => smt.BVAnd(inState(c.stateId), c.guard)))
      smt.Signal(signalName, en)
    }
  }

  private def connectMethodArgs(mappings: Seq[PasoStateGuardedMapping], methods: Iterable[MethodInfo]): Iterable[smt.Signal] = {
    val argsToMappings = mappings.groupBy(_.map.arg)
    methods.flatMap { m => m.args.map { case (a, width) =>
      val arg = smt.BVSymbol(m.parent + "." + a, width)
      val prev = arg.rename(arg.name + "$prev")
      val value = argsToMappings.getOrElse(arg, List()).foldLeft[smt.BVExpr](prev){(other, m) =>
        smt.BVIte(smt.BVAnd(inState(m.stateId), m.map.guard), m.map.update, other)
      }
      smt.Signal(arg.name, value)
    }}
  }

  private def prevMethodArgs(methods: Iterable[MethodInfo]): Iterable[smt.State] = {
    methods.flatMap { m => m.args.map { case (a, width) =>
      val arg = smt.BVSymbol(m.parent + "." + a, width)
      val prev = arg.rename(arg.name + "$prev")
      smt.State(prev, init=None, next=Some(arg))
    }}
  }

  private def encodeStateEdges(state: smt.BVSymbol, edges: Iterable[PasoStateEdge]): smt.State = {
    // we want to compute the next state based on the current state and predicates
    val invalidState = smt.BVLiteral((BigInt(1) << stateBits) - 1, stateBits)
    val next = edges.groupBy(_.to).foldLeft[smt.BVExpr](invalidState) { case (other, (nextState, edges)) =>
      val guard = smt.BVOr(edges.map(e => smt.BVAnd(inState(e.from), e.guard)))
      smt.BVIte(guard, smt.BVLiteral(nextState, stateBits), other)
    }
    smt.State(state, init = Some(smt.BVLiteral(0, stateBits)), next = Some(next))
  }

  /** the idea here is to group predicates that just have different guards */
  private def compactEncodePredicates(preds: Iterable[PasoStateGuarded], prefix: String, lbl: smt.SignalLabel, invert: Boolean): Iterable[smt.Signal] = {
    val notTriviallyTrue = preds.filterNot(_.pred.pred == smt.True())
    val groups = notTriviallyTrue.groupBy(_.pred.pred.toString)
    groups.zipWithIndex.map { case ((_, ps), i) =>
      val guard = smt.BVOr(ps.map(p => smt.BVAnd(inState(p.stateId), p.pred.guard)))
      val pred = ps.head.pred.pred
      val expr = smt.BVImplies(guard, pred)
      smt.Signal(s"${prefix}_$i", if(invert) not(expr) else expr, lbl)
    }
  }

  private def not(e: smt.BVExpr): smt.BVExpr = e match {
    case smt.BVNot(inner) => inner
    case o => smt.BVNot(o)
  }
}
