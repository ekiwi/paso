// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.mc

import maltese.mc
import maltese.smt.{BVSymbol, SMTExpr, SMTSymbol}

case class State(sym: SMTSymbol, init: Option[SMTExpr], next: Option[SMTExpr])
case class Signal(name: String, e: SMTExpr, lbl: SignalLabel = IsNode) {
  def toSymbol: SMTSymbol = SMTSymbol.fromExpr(name, e)
}
case class TransitionSystem(name: String, inputs: List[BVSymbol], states: List[State], signals: List[Signal]) {
  def serialize: String = TransitionSystem.serialize(this)
}

sealed trait SignalLabel
case object IsNode extends SignalLabel
case object IsOutput extends SignalLabel
case object IsConstraint extends SignalLabel
case object IsBad extends SignalLabel
case object IsFair extends SignalLabel
case object IsNext extends SignalLabel
case object IsInit extends SignalLabel

object SignalLabel {
  private val labels = Seq(IsNode, IsOutput, IsConstraint, IsBad, IsFair, IsNext, IsInit)
  val labelStrings = Seq("node", "output", "constraint", "bad", "fair", "next", "init")
  val labelToString: SignalLabel => String = labels.zip(labelStrings).toMap
  val stringToLabel: String => SignalLabel = labelStrings.zip(labels).toMap
}

object TransitionSystem {
  def serialize(sys: TransitionSystem): String = {
    (Iterator(sys.name) ++
      sys.inputs.map(i => s"input ${i.name} : ${SMTExpr.serializeType(i)}") ++
      sys.signals.map(s => s"${SignalLabel.labelToString(s.lbl)} ${s.name} : ${SMTExpr.serializeType(s.e)} = ${s.e}") ++
      sys.states.map(s => s"state ${s.sym.name} : ${SMTExpr.serializeType(s.sym)}\n  [init] ${s.init}\n  [next] ${s.next}")
      ).mkString("\n")
  }

  /** prefixes all signal names with the name of the transition system */
  def prefixSignals(sys: TransitionSystem): TransitionSystem = {
    val prefix = sys.name + "."
    val names: Iterable[String] = sys.inputs.map(_.name) ++ sys.states.map(_.sym.name) ++ sys.signals.map(_.name)
    val renames = names.map(n => n -> (prefix + n)).toMap
    val inputs = sys.inputs.map(i => i.rename(renames.getOrElse(i.name, i.name)))
    def r(e: SMTExpr): SMTExpr = rename(renames)(e)
    val states = sys.states.map(s => mc.State(r(s.sym).asInstanceOf[SMTSymbol], s.init.map(r), s.next.map(r)))
    val signals = sys.signals.map(s => s.copy(name = renames(s.name), e = r(s.e)))
    TransitionSystem(sys.name, inputs, states, signals)
  }

  private def rename(map: Map[String, String])(e: SMTExpr): SMTExpr = e match {
    case sym : SMTSymbol => sym.rename(map.getOrElse(sym.name, sym.name))
    case other => other.mapExpr(rename(map))
  }

  def combine(name: String, sys: List[TransitionSystem]): TransitionSystem = {
    TransitionSystem(name,
      inputs = sys.flatMap(_.inputs),
      states = sys.flatMap(_.states),
      signals = sys.flatMap(_.signals)
    )
  }

  /** combines all properties into one */
  def combineProperties(sys: TransitionSystem): TransitionSystem = {
    ???
  }

  /** inlines all nodes which could lead to an exponential blowup in size */
  def inlineNodes(sys: TransitionSystem): TransitionSystem = {
    ???
  }
}
