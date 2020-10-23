// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import maltese.smt

/** prefixes all signal names with the name of the transition system */
object NamespaceTransitionSystem {
  def run(sys: smt.TransitionSystem): smt.TransitionSystem = {
    val prefix = sys.name + "."
    val names: Iterable[String] = sys.inputs.map(_.name) ++ sys.states.map(_.sym.name) ++ sys.signals.map(_.name)
    val renames = names.map(n => n -> (prefix + n)).toMap
    val inputs = sys.inputs.map(i => i.rename(renames.getOrElse(i.name, i.name)))
    def r(e: smt.SMTExpr): smt.SMTExpr = rename(renames)(e)
    val states = sys.states.map(s => smt.State(r(s.sym).asInstanceOf[smt.SMTSymbol], s.init.map(r), s.next.map(r)))
    val signals = sys.signals.map(s => s.copy(name = renames(s.name), e = r(s.e)))
    smt.TransitionSystem(sys.name, inputs, states, signals)
  }

  private def rename(map: Map[String, String])(e: smt.SMTExpr): smt.SMTExpr = e match {
    case sym : smt.SMTSymbol => sym.rename(map.getOrElse(sym.name, sym.name))
    case other => other.mapExpr(rename(map))
  }
}
