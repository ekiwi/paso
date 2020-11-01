// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>


package maltese.passes

import maltese.mc.TransitionSystem
import maltese.mc

/** Removed all signals that are not used. */
object DeadCodeElimination extends Pass {
  override def name: String = "DeadCodeElimination"

  override def run(sys: TransitionSystem): TransitionSystem = {
    val useCount = Analysis.countUses(sys.signals)
    val eliminatedStates = sys.states.map(_.sym.name).filter(n => useCount(n) == 0).toSet
    val signals = sys.signals.filterNot { s => s.lbl match {
      case mc.IsNode => useCount(s.name) == 0
      case mc.IsNext | mc.IsInit =>
        val state = s.name.split('.').dropRight(1).mkString(".")
        eliminatedStates.contains(state)
      case _ => false
    }}
    val states = sys.states.filterNot(s => eliminatedStates.contains(s.sym.name))
    sys.copy(signals = signals, states = states)
  }
}
