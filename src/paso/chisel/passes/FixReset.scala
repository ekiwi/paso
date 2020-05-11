// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel.passes

import firrtl.ir

// somehow when making a submodule the toplevel module, we need to replace the reset
object FixReset {
  private val UInt1 = ir.UIntType(ir.IntWidth(1))
  private def onPort(p: ir.Port): ir.Port = if(p.name != "reset") { p } else { p.copy(tpe = UInt1) }
  def apply(m: ir.Module): ir.Module = {
    val p = m.ports.map(onPort)
    m.copy(ports = p)
  }
}
