// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel.passes

import firrtl.ir
import uclid.smt

import scala.collection.mutable

case class RemoveInstances() {
  private val instances = mutable.HashMap[String, String]()
  private def onStmt(s: ir.Statement): ir.Statement = s match {
    case ir.DefInstance(_, name, module, _) =>
      instances += (name -> module)
      ir.EmptyStmt
    case c : ir.Connect =>
      val prefix = c.loc.serialize.split('.').head
      if(instances.contains(prefix)) ir.EmptyStmt else c
    case other => other.mapStmt(onStmt)
  }
  def mkBitVec(value: BigInt, tpe: ir.Type): smt.Expr = tpe match {
    case ir.UIntType(ir.IntWidth(w)) => if(w > 1) smt.BitVectorLit(value, w.toInt) else smt.BooleanLit(value != 0)
    case ir.SIntType(ir.IntWidth(w)) => if(w > 1) smt.BitVectorLit(value, w.toInt) else smt.BooleanLit(value != 0)
  }
  def run(m: ir.Module): (ir.Module, Map[String, String]) = {
    val newM = m.mapStmt(onStmt).asInstanceOf[ir.Module]
    (newM, instances.toMap)
  }
}
