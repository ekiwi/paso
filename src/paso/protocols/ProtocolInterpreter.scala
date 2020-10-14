// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.backends.experimental.smt.FirrtlToSMT
import firrtl.ir

import scala.collection.mutable

abstract class ProtocolInterpreter(protocol: firrtl.CircuitState) {
  case class Loc(block: Int, stmt: Int) { override def toString = f"$block:$stmt" }

  // callbacks that need to be implemented
  protected def onSet(info: ir.Info, loc: String, expr: ir.Expression): Unit
  protected def onUnSet(info: ir.Info, loc: String): Unit
  protected def onAssert(info: ir.Info, expr: ir.Expression): Unit
  protected def onGoto(g: Goto): Unit
  protected def onStep(info: ir.Info, loc: Loc, name: String): Unit
  protected def onFork(info: ir.Info, loc: Loc, name: String): Unit

  // The Protocol Compiler should make sure that the circuit is of a valid form!
  assert(protocol.circuit.modules.size == 1)
  protected val name = protocol.circuit.main
  protected val module = protocol.circuit.modules.head.asInstanceOf[ir.Module]
  protected val blocks = module.body.asInstanceOf[ir.Block].stmts.map(_.asInstanceOf[ir.Block]).toArray
  private val ioPorts = module.ports.filter(_.name.startsWith("io"))
  protected val io = ioPorts.map(p => p.name -> toWidth(p.tpe)).toMap
  // RTL implementation inputs are outputs to the protocol and vice versa!
  protected val inputs = ioPorts.filter(_.direction == ir.Output).map(p => p.name -> toWidth(p.tpe)).toMap
  protected val outputs = ioPorts.filter(_.direction == ir.Input).map(p => p.name -> toWidth(p.tpe)).toMap
  protected val args = module.ports.filter(_.name.startsWith("arg")).map(p => p.name -> toWidth(p.tpe)).toMap
  protected val rets = module.ports.filter(_.name.startsWith("ret")).map(p => p.name -> toWidth(p.tpe)).toMap
  protected val steps = protocol.annotations.collect { case StepAnnotation(wire) =>
    assert(wire.circuit == protocol.circuit.main)
    assert(wire.module == module.name)
    wire.ref
  }.toSet
  protected val forks = protocol.annotations.collect { case ForkAnnotation(wire) =>
    assert(wire.circuit == protocol.circuit.main)
    assert(wire.module == module.name)
    wire.ref
  }.toSet

  protected def onBlock(id: Int): Unit = {
    assert(blocks.length > id && id >= 0, f"Invalid block id: $id")
    val b = blocks(id)
    assert(b.stmts.head == BlockId(id), f"Block id mismatch! ${b.stmts.head.serialize} != $id")
    b.stmts.drop(1).zipWithIndex.foreach{ case (s,i) => onStmt(s, Loc(id, i)) }
  }

  protected def onStmt(s: ir.Statement, loc: Loc): Unit = s match {
    case n : ir.DefNode => throw new RuntimeException(f"Found non-inlined node: ${n.serialize}")
    case ir.Connect(info, ir.Reference(loc, _, _, _), expr) =>
      assert(inputs.contains(loc), f"$loc is not an input, can only assign values to RTL inputs")
      onSet(info, loc, expr)
    case ir.IsInvalid(info, ir.Reference(loc, _, _, _)) =>
      assert(inputs.contains(loc), f"$loc is not an input, can only assign values to RTL inputs")
      onUnSet(info, loc)
    case ir.Verification(ir.Formal.Assert, info, _, pred, en, _) =>
      assert(en == ir.UIntLiteral(1,ir.IntWidth(1)), f"Expected enabled to be true! Not: ${en.serialize}")
      onAssert(info, pred)
    case g : Goto => onGoto(g)
    case ir.DefWire(info, name, _) if steps.contains(name) => onStep(info, loc, name)
    case ir.DefWire(info, name, _) if forks.contains(name) => onFork(info, loc, name)
    case other => throw new RuntimeException(f"Unexpected statement: ${other.serialize}")
  }

  private def toWidth(tpe: ir.Type): Int = FirrtlToSMT.toWidth(tpe)
}

sealed trait ProtocolResult
case object ProtocolFail extends ProtocolResult
case object ProtocolSuccess extends ProtocolResult

/*
class ConcreteProtocolInterpreter(protocol: Protocol) extends ProtocolInterpreter(protocol) {

  def run(methodIO: Map[String, BigInt]): ProtocolResult = {
    ProtocolFail
  }

}
*/