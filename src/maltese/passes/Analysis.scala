// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.passes

import maltese.mc.Signal
import maltese.smt._

import scala.collection.mutable

object Analysis {
  def findSymbols(e: SMTExpr): List[SMTSymbol] = e match {
    case s: BVSymbol => List(s)
    case s: ArraySymbol => List(s)
    case other => other.children.flatMap(findSymbols)
  }

  def countUses(signals: Iterable[Signal]): String => Int = {
    // count how often a symbol is used
    implicit val useCount = mutable.HashMap[String, Int]().withDefaultValue(0)
    signals.map(_.e).foreach(countUses)
    useCount
  }

  private def countUses(e: SMTExpr)(implicit useCount: mutable.Map[String, Int]): Unit = e match {
    case BVSymbol(name, _) => useCount(name) += 1
    case ArraySymbol(name, _, _) => useCount(name) += 1
    case other => other.foreachExpr(countUses)
  }
}
