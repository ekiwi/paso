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
  private val state = smt.BVSymbol(signalPrefix + "state", stateBits)
  private val inState = auto.states.map(s => smt.BVSymbol(signalPrefix + s"state_is_${s.id}", 1)).toArray
  private val invalidState = smt.BVSymbol(signalPrefix + "state_is_invalid", 1)

  def run(): smt.TransitionSystem = {
    // TODO: deal with multiple copies of the same protocol/transaction

    // connect method enabled inputs and arguments
    val methodInputs = connectMethodEnabled(auto.commits, auto.untimed.methods) ++
      connectMethodArgs(auto.mappings, auto.untimed.methods)





    ???
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
    methods.map { m => m.args.map { a =>
      val argName = m.fullIoName + a
      println(argName)
    }}
    ???
  }
}
