// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.passes.PassException
import paso.verification.UntimedModel
import maltese.smt
import maltese.smt.solvers.Yices2

import scala.collection.mutable

/**
 * Combines the untimed module and all its protocols into a "Paso Automaton" transition system.
 *
 * */
class PasoAutomatonEncoder(untimed: UntimedModel, protocols: Iterable[ProtocolGraph]) {
  /** Identifies a transition in a particular protocol as well as the copyId of the protocol in case it needed to be duplicated */
  private case class Loc(name: String, transition: Int, copyId: Int = 0) {
    override def toString: String = s"$name$$$copyId@$transition"
  }
  private val transitionMap: Map[String, Transition] =
    protocols.flatMap { p => p.transitions.zipWithIndex.map { case (t, i) => s"${p.name}@$i" -> t }}.toMap
  private def transition(loc: Loc): Transition = transitionMap(s"${loc.name}@${loc.transition}")

  /** States are characterized by the active protocols and whether a new protocol is going to be started. */
  private case class State(id: Int, active: Seq[Loc], fork: Boolean, next: List[NextState]) {
    def toIndex: String = "{" + active.map(_.toString).sorted.mkString(", ") + "}" + (if(fork) " (F)" else "")
  }
  private case class NextState(guard: smt.BVExpr, stateId: Int)
  /** States are accumulated as we explore the possible execution of the combined protocols. */
  private val states = mutable.HashMap[String, State]()

  case class StateGuarded(stateId: Int, guard: smt.BVExpr, pred: smt.BVExpr)
  /** collects all assumptions over the inputs, depending on the state */
  private val inputAssumptions = mutable.ArrayBuffer[StateGuarded]()

  /** collects all assertions depending on the state */
  private val assertions = mutable.ArrayBuffer[StateGuarded]()

  case class StateGuardedMapping(stateId: Int, map: GuardedMapping)
  /** collects all argument mappings for all protocols depending on the state */
  private val mappings = mutable.ArrayBuffer[StateGuardedMapping]()

  def run(): smt.TransitionSystem = ???

  private val solver = Yices2()
  private def isFeasible(cond: smt.BVExpr): Boolean = solver.check(cond, produceModel = false).isSat
}