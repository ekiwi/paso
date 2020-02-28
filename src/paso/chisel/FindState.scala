// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import uclid.smt
import firrtl.ir
import scala.collection.mutable

case class FindState(c: ir.Circuit) {
  private val mods = c.modules.collect{ case m: ir.Module => m.name -> m}.toMap
  private val state = mutable.ArrayBuffer[smt.Symbol]()
  private def onStmt(prefix: String, s: ir.Statement): Unit = s match {
    case ir.DefRegister(_, name, tpe, _, _, _) =>
      state.append(smt.Symbol(prefix + name, firrtlToSmtType(tpe)))
    case ir.DefMemory(_, name, tpe, depth, _,  _, _,_,_,_) =>
      state.append(smt.Symbol(prefix + name, firrtlToSmtType(tpe, depth)))
    case ir.DefInstance(_, name, module) if mods.contains(module) =>
      mods(module).body.foreachStmt(onStmt(prefix + name + ".", _))
    case other => other.foreachStmt(onStmt(prefix, _))
  }
  def run(): Seq[smt.Symbol] = {
    onStmt("", mods(c.main).body)
    state
  }
}
