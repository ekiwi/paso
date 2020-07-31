// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel.passes

import firrtl.ir
import uclid.smt

import scala.collection.mutable

case class State(name: String, tpe: ir.Type, init: Option[smt.Expr] = None)
case class FindState(c: ir.Circuit) {
  private val mods = c.modules.collect{ case m: ir.Module => m.name -> m}.toMap
  private val state = mutable.ArrayBuffer[State]()
  private def onStmt(prefix: String, s: ir.Statement): Unit = s match {
    case ir.DefRegister(_, name, tpe, _, _, ir.Reference(_, _, _, _)) =>
      state.append(State(prefix + name, tpe))
    case ir.DefRegister(_, name, tpe, _, _, ir.UIntLiteral(value, ir.IntWidth(w))) =>
      state.append(State(prefix + name, tpe, Some(mkBitVec(value, tpe))))
    case ir.DefRegister(_, name, tpe, _, _, ir.SIntLiteral(value, ir.IntWidth(w))) =>
      state.append(State(prefix + name, tpe, Some(mkBitVec(value, tpe))))
    case otherReg: ir.DefRegister => throw new NotImplementedError(s"TODO: handle $otherReg")
    case ir.DefMemory(_, name, tpe, depth, _,  _, _,_,_,_) =>
      state.append(State(prefix + name, ir.VectorType(tpe, depth.toInt)))
    case firrtl.CDefMemory(_, name, tpe, depth, _,  _) =>
      state.append(State(prefix + name, ir.VectorType(tpe, depth.toInt)))
    case ir.DefInstance(_, name, module, _) if mods.contains(module) =>
      mods(module).body.foreachStmt(onStmt(prefix + name + ".", _))
    case other => other.foreachStmt(onStmt(prefix, _))
  }
  def mkBitVec(value: BigInt, tpe: ir.Type): smt.Expr = tpe match {
    case ir.UIntType(ir.IntWidth(w)) => if(w > 1) smt.BitVectorLit(value, w.toInt) else smt.BooleanLit(value != 0)
    case ir.SIntType(ir.IntWidth(w)) => if(w > 1) smt.BitVectorLit(value, w.toInt) else smt.BooleanLit(value != 0)
  }
  def run(): Seq[State] = {
    onStmt("", mods(c.main).body)
    state
  }
}

case class FindModuleState() {
  private val state = mutable.ArrayBuffer[State]()
  private def onStmt(prefix: String, s: ir.Statement): Unit = s match {
    case ir.DefRegister(_, name, tpe, _, _, ir.Reference(_, _, _, _)) =>
      state.append(State(prefix + name, tpe))
    case ir.DefRegister(_, name, tpe, _, _, ir.UIntLiteral(value, ir.IntWidth(w))) =>
      state.append(State(prefix + name, tpe, Some(mkBitVec(value, tpe))))
    case ir.DefRegister(_, name, tpe, _, _, ir.SIntLiteral(value, ir.IntWidth(w))) =>
      state.append(State(prefix + name, tpe, Some(mkBitVec(value, tpe))))
    case otherReg: ir.DefRegister => throw new NotImplementedError(s"TODO: handle $otherReg")
    case ir.DefMemory(_, name, tpe, depth, _,  _, _,_,_,_) =>
      state.append(State(prefix + name, ir.VectorType(tpe, depth.toInt)))
    case firrtl.CDefMemory(_, name, tpe, depth, _,  _) =>
      state.append(State(prefix + name, ir.VectorType(tpe, depth.toInt)))
    case other => other.foreachStmt(onStmt(prefix, _))
  }
  def mkBitVec(value: BigInt, tpe: ir.Type): smt.Expr = tpe match {
    case ir.UIntType(ir.IntWidth(w)) => if(w > 1) smt.BitVectorLit(value, w.toInt) else smt.BooleanLit(value != 0)
    case ir.SIntType(ir.IntWidth(w)) => if(w > 1) smt.BitVectorLit(value, w.toInt) else smt.BooleanLit(value != 0)
  }
  def run(m: ir.Module): Seq[State] = {
    onStmt("", m.body)
    state
  }
}