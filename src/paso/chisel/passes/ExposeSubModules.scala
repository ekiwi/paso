// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel.passes

import firrtl.ir

import scala.collection.mutable

class ExposeSubModules(c: ir.Circuit, toBeReplaced: Set[String]) {
  private val mods = c.modules.collect{ case m: ir.Module => m.name -> m}.toMap
  private val ports = mutable.ArrayBuffer[ir.Port]()

  private def exposeInstance(prefix: String, info: ir.Info, name: String, tpe: ir.Type): ir.Statement = {
    // add a new port to the toplevel module and delete the instance definition
    // TODO: support hierarchical replacement
    ports.append(ir.Port(info, name, ir.Input, tpe))
    ir.EmptyStmt
  }

  private def onInstance(prefix: String, d: firrtl.WDefInstance): ir.Statement = {
    val doReplace = toBeReplaced.contains(prefix + d.name)
    if(doReplace) {
      exposeInstance(prefix, d.info, d.name, d.tpe)
    } else {
      throw new NotImplementedError("TODO: support submodules that are NOT replaced!")
      d.mapStmt(onStmt(prefix, _))
    }
  }

  private def onStmt(prefix: String, s: ir.Statement): ir.Statement = s match {
    case _ : ir.DefInstance =>
      throw new RuntimeException("Expected a working instance since we need to know the reference type!")
    case d : firrtl.WDefInstance => onInstance(prefix, d)
    case other => other.mapStmt(onStmt(prefix, _))
  }

  def apply(): ir.Circuit= {
    val main = mods(c.main)
    val newBody = onStmt(c.main + ".", main.body)
    // TODO: support submodules that are not replaced
    c.copy(modules = Seq(main.copy(body = newBody, ports = main.ports ++ ports)))
  }
}
