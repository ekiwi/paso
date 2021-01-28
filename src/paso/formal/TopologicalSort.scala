// Copyright 2020 The Regents of the University of California
// Copyright 2020 SiFive
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>
// this file was originally written as part of the firrtl compiler and then translated to work on the maltese.smt
// data structures

package paso.formal

import firrtl.graph.MutableDiGraph
import maltese.mc.TransitionSystem
import maltese.smt

import scala.collection.mutable

object TopologicalSort {

  /** Ensures that all signals in the resulting system are topologically sorted. */
  def run(sys: TransitionSystem): TransitionSystem = {
    val inputsAndStates = sys.inputs.map(_.name) ++ sys.states.map(_.sym.name)
    val signalOrder = sort(sys.signals.map(s => s.name -> s.e), inputsAndStates)
    // TODO: maybe sort init expressions of states (this should not be needed most of the time)
    signalOrder match {
      case None => sys
      case Some(order) =>
        val signalMap = sys.signals.map(s => s.name -> s).toMap
        // we flatMap over `get` in order to ignore inputs/states in the order
        sys.copy(signals = order.flatMap(signalMap.get).toList)
    }
  }

  private def sort(signals: Iterable[(String, smt.SMTExpr)], globalSignals: Iterable[String]): Option[Iterable[String]] = {
    val known = new mutable.HashSet[String]() ++ globalSignals
    var needsReordering = false
    val digraph = new MutableDiGraph[String]
    signals.foreach {
      case (name, expr) =>
        digraph.addVertex(name)
        val uniqueDependencies = mutable.LinkedHashSet[String]() ++ findDependencies(expr)
        uniqueDependencies.foreach { d =>
          if (!known.contains(d)) { needsReordering = true }
          digraph.addPairWithEdge(name, d)
        }
        known.add(name)
    }
    if (needsReordering) {
      Some(digraph.linearize.reverse)
    } else { None }
  }

  private def findDependencies(expr: smt.SMTExpr): List[String] = expr match {
    case smt.BVSymbol(name, _)       => List(name)
    case smt.ArraySymbol(name, _, _) => List(name)
    case other                   => other.children.flatMap(findDependencies)
  }
}