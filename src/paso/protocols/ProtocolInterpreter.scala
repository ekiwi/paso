// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.annotations.CircuitTarget
import firrtl.ir

object ProtocolInterpreter {
  case class Loc(block: Int, stmt: Int) { override def toString = f"$block:$stmt" }
}

case class Proto(info: ProtocolInfo, graph: UGraph) {
  def name: String = info.name
  def stickyInputs: Boolean = info.stickyInputs
}

case class ProtocolInfo(name: String,
  args: Map[String, Int], rets: Map[String, Int],
  inputs: Map[String, Int], outputs: Map[String, Int],
  ioPrefix: String, methodPrefix: String, stickyInputs: Boolean)

abstract class ProtocolInterpreter(protocol: firrtl.CircuitState, stickyInputs: Boolean) {
  import ProtocolInterpreter.Loc

  // The Protocol Compiler should make sure that the circuit is of a valid form!
  assert(protocol.circuit.modules.size == 1)
  private val module = protocol.circuit.modules.head.asInstanceOf[ir.Module]
  private val blocks = module.body.asInstanceOf[ir.Block].stmts.map(_.asInstanceOf[ir.Block]).toArray
  protected def blockCount = blocks.length
  val prefixAnno = protocol.annotations.collectFirst{ case a : ProtocolPrefixAndNameAnnotation => a }.get
  val ioPrefix = prefixAnno.ioPrefix
  private val ioPorts = module.ports.filter(_.name.startsWith(ioPrefix))
  protected val io = ioPorts.map(p => p.name -> toWidth(p.tpe)).toMap
  // RTL implementation inputs are outputs to the protocol and vice versa!
  protected val inputs = ioPorts.filter(_.direction == ir.Output).map(p => p.name -> toWidth(p.tpe)).toMap
  protected val outputs = ioPorts.filter(_.direction == ir.Input).map(p => p.name -> toWidth(p.tpe)).toMap
  val methodPrefix = prefixAnno.methodPrefix
  protected val args = module.ports.filter(_.name.startsWith(methodPrefix + "arg")).map(p => p.name -> toWidth(p.tpe)).toMap
  protected val rets = module.ports.filter(_.name.startsWith(methodPrefix + "ret")).map(p => p.name -> toWidth(p.tpe)).toMap
  // we treat the state at the beginning of the protocol as an implicit start step
  private val startStepAnnotation =
    StepAnnotation(CircuitTarget(module.name).module(module.name).ref("start"), doFork = false, isFinal = false)
  protected val steps = (protocol.annotations.collect { case a : StepAnnotation =>
    assert(a.target.circuit == protocol.circuit.main)
    assert(a.target.module == module.name)
    a.target.ref -> a
  } :+ ("start" -> startStepAnnotation)).toMap
  protected val stepOrder = protocol.annotations.collectFirst { case StepOrderAnnotation(steps, _) => steps }.get
  protected val name = s"${prefixAnno.specPrefix}${prefixAnno.methodName}"
  protected def getInfo: ProtocolInfo = ProtocolInfo(name, args, rets, inputs, outputs, ioPrefix, methodPrefix, stickyInputs)

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
      DoSet(info, loc, isSticky = stickyInputs, expr)
    case ir.IsInvalid(info, ir.Reference(loc, _, _, _)) =>
      assert(inputs.contains(loc), f"$loc is not an input, can only assign values to RTL inputs")
      DoUnSet(info, loc)
    case ir.Verification(ir.Formal.Assert, info, _, pred, en, _) =>
      assert(en == ir.UIntLiteral(1,ir.IntWidth(1)), f"Expected enabled to be true! Not: ${en.serialize}")
      DoAssert(info, pred)
    case g : Goto => g
    case ir.DefWire(info, name, _) if steps.contains(name) => DoStep(info, loc, name)
    case other => throw new RuntimeException(f"Unexpected statement: ${other.serialize}")
  }

  private def toWidth(tpe: ir.Type): Int = firrtl.bitWidth(tpe).toInt
}

sealed trait ProtocolResult
case object ProtocolFail extends ProtocolResult
case object ProtocolSuccess extends ProtocolResult

trait ProtocolStatement
case class DoSet(info: ir.Info, loc: String, isSticky: Boolean, expr: ir.Expression) extends ProtocolStatement
case class DoUnSet(info: ir.Info, loc: String) extends ProtocolStatement
case class DoAssert(info: ir.Info, expr: ir.Expression) extends ProtocolStatement
case class DoStep(info: ir.Info, loc: ProtocolInterpreter.Loc, name: String) extends ProtocolStatement