// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.backends.experimental.smt.FirrtlToSMT
import firrtl.ir

object ProtocolInterpreter {
  case class Loc(block: Int, stmt: Int) { override def toString = f"$block:$stmt" }
}

abstract class ProtocolInterpreter(protocol: firrtl.CircuitState) {
  import ProtocolInterpreter.Loc

  // The Protocol Compiler should make sure that the circuit is of a valid form!
  assert(protocol.circuit.modules.size == 1)
  protected val name = protocol.circuit.main
  protected val module = protocol.circuit.modules.head.asInstanceOf[ir.Module]
  protected val blocks = module.body.asInstanceOf[ir.Block].stmts.map(_.asInstanceOf[ir.Block]).toArray
  val prefixAnno = protocol.annotations.collectFirst{ case a : ProtocolPrefixAnnotation => a }
  val ioPrefix = prefixAnno.map(_.ioPrefix).getOrElse("io_")
  private val ioPorts = module.ports.filter(_.name.startsWith(ioPrefix))
  protected val io = ioPorts.map(p => p.name -> toWidth(p.tpe)).toMap
  // RTL implementation inputs are outputs to the protocol and vice versa!
  protected val inputs = ioPorts.filter(_.direction == ir.Output).map(p => p.name -> toWidth(p.tpe)).toMap
  protected val outputs = ioPorts.filter(_.direction == ir.Input).map(p => p.name -> toWidth(p.tpe)).toMap
  val methodPrefix = prefixAnno.map(_.methodPrefix).getOrElse("")
  protected val args = module.ports.filter(_.name.startsWith(methodPrefix + "arg")).map(p => p.name -> toWidth(p.tpe)).toMap
  protected val rets = module.ports.filter(_.name.startsWith(methodPrefix + "ret")).map(p => p.name -> toWidth(p.tpe)).toMap
  protected val steps = protocol.annotations.collect { case StepAnnotation(wire, doFork) =>
    assert(wire.circuit == protocol.circuit.main)
    assert(wire.module == module.name)
    wire.ref -> doFork
  }.toMap

  protected def onBlock(id: Int): Unit = getBlock(id).foreach { case (loc, s) => onStmt(s, loc) }

  /** returns the instructions of the basic block */
  protected def getBlock(id: Int): IndexedSeq[(Loc, ir.Statement)] = {
    assert(blocks.length > id && id >= 0, f"Invalid block id: $id")
    val b = blocks(id)
    assert(b.stmts.head == BlockId(id), f"Block id mismatch! ${b.stmts.head.serialize} != $id")
    b.stmts.drop(1).zipWithIndex.map{ case (s,i) => (Loc(id, i), s) }.toIndexedSeq
  }

  protected def parseStmt(s: ir.Statement, loc: Loc): ProtocolStatement = s match {
    case n : ir.DefNode => throw new RuntimeException(f"Found non-inlined node: ${n.serialize}")
    case ir.Connect(info, ir.Reference(loc, _, _, _), expr) =>
      assert(inputs.contains(loc), f"$loc is not an input, can only assign values to RTL inputs")
      Set(info, loc, expr)
    case ir.IsInvalid(info, ir.Reference(loc, _, _, _)) =>
      assert(inputs.contains(loc), f"$loc is not an input, can only assign values to RTL inputs")
      UnSet(info, loc)
    case ir.Verification(ir.Formal.Assert, info, _, pred, en, _) =>
      assert(en == ir.UIntLiteral(1,ir.IntWidth(1)), f"Expected enabled to be true! Not: ${en.serialize}")
      Assert(info, pred)
    case g : Goto => g
    case ir.DefWire(info, name, _) if steps.contains(name) => Step(info, loc, name, steps(name))
    case other => throw new RuntimeException(f"Unexpected statement: ${other.serialize}")
  }

  private def toWidth(tpe: ir.Type): Int = FirrtlToSMT.toWidth(tpe)
}

sealed trait ProtocolResult
case object ProtocolFail extends ProtocolResult
case object ProtocolSuccess extends ProtocolResult

trait ProtocolStatement
case class Set(info: ir.Info, loc: String, expr: ir.Expression) extends ProtocolStatement
case class UnSet(info: ir.Info, loc: String) extends ProtocolStatement
case class Assert(info: ir.Info, expr: ir.Expression) extends ProtocolStatement
case class Step(info: ir.Info, loc: ProtocolInterpreter.Loc, name: String, fork: Boolean) extends ProtocolStatement

/*
class ConcreteProtocolInterpreter(protocol: Protocol) extends ProtocolInterpreter(protocol) {

  def run(methodIO: Map[String, BigInt]): ProtocolResult = {
    ProtocolFail
  }

}
*/