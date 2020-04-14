// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel.passes

import scala.collection.mutable
import firrtl.ir
import firrtl.ir.NoInfo

case class ReplaceMemReadWithVectorAccess(memTypes: Map[String, ir.VectorType]) {
  private def replacePort(p: firrtl.CDefMPort): ir.Statement = {
    require(p.direction == firrtl.MRead || p.direction == firrtl.MInfer, s"Only read ports can be replaced not: ${p.direction}")
    require(memTypes.contains(p.mem), s"Read port ${p.name} refers to unknown memory ${p.mem}: ${p.serialize}")
    val memTpe = memTypes(p.mem)
    val access = ir.SubAccess(ir.Reference(p.mem, memTpe), p.exps.head, memTpe.tpe)
    ir.DefNode(NoInfo, p.name, access)
  }

  private def onStmt(s: ir.Statement): ir.Statement = s match {
    case p : firrtl.CDefMPort => replacePort(p)
    case other => other.mapStmt(onStmt)
  }
  def apply(c: ir.Circuit): ir.Circuit = {
    assert(c.modules.length == 1)
    c.copy(modules = Seq(c.modules.head.asInstanceOf[ir.Module].mapStmt(onStmt)))
  }
}
