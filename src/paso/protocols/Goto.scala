// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.ir

case class Goto(info: ir.Info, cond: ir.Expression, conseq: Int, alt: Int) extends ir.Statement with ProtocolStatement {
  override def mapStmt(f: ir.Statement => ir.Statement) = this
  override def mapExpr(f: ir.Expression => ir.Expression) = Goto(info, f(cond), conseq, alt)
  override def mapType(f: ir.Type => ir.Type) = this
  override def mapString(f: String => String) = this
  override def mapInfo(f: ir.Info => ir.Info) = Goto(f(info), cond, conseq, alt)
  override def foreachStmt(f: ir.Statement => Unit): Unit = ()
  override def foreachExpr(f: ir.Expression => Unit): Unit = f(cond)
  override def foreachType(f: ir.Type => Unit): Unit = ()
  override def foreachString(f: String => Unit): Unit = ()
  override def foreachInfo(f: ir.Info => Unit): Unit = f(info)
  override def serialize = cond match {
    case u : ir.UIntLiteral if u.value == 1 => s"goto $conseq"
    case u : ir.UIntLiteral if u.value == 0 => s"goto $alt"
    case other => s"when ${other.serialize} goto $conseq else goto $alt"
  }
  def getTargets: List[Int] = cond match {
    case u : ir.UIntLiteral if u.value == 1 => List(conseq)
    case u : ir.UIntLiteral if u.value == 0 => List(alt)
    case other => List(conseq, alt)
  }
}

object Goto {
  def apply(info: ir.Info, conseq: Int): Goto = Goto(info, ir.UIntLiteral(1, ir.IntWidth(1)), conseq, -1)
}

case class BlockId(id: Int) extends ir.Statement {
  override def mapStmt(f: ir.Statement => ir.Statement) = this
  override def mapExpr(f: ir.Expression => ir.Expression) = this
  override def mapType(f: ir.Type => ir.Type) = this
  override def mapString(f: String => String) = this
  override def mapInfo(f: ir.Info => ir.Info) = this
  override def foreachStmt(f: ir.Statement => Unit): Unit = ()
  override def foreachExpr(f: ir.Expression => Unit): Unit = ()
  override def foreachType(f: ir.Type => Unit): Unit = ()
  override def foreachString(f: String => Unit): Unit = ()
  override def foreachInfo(f: ir.Info => Unit): Unit = ()
  override def serialize = s"$id:"
}
