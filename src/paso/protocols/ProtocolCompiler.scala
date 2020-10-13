// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.ir
import firrtl.options.Dependency
import firrtl.passes.PassException
import firrtl.stage.{Forms, TransformManager}
import firrtl.{CircuitState, DependencyAPIMigration, Transform}

object ProtocolCompiler {
  val StepFunctionCode = 23456
  val ForkFunctionCode = 34678

  private val compiler = new TransformManager(Seq(Dependency(CheckStatementsPass), Dependency(ProtocolNormalizationPass)))

  def run(state: CircuitState): CircuitState = {
    println(compiler.prettyPrint())
    compiler.runTransform(state)
  }
}

/** Normalizes a protocol program to make it easier to interpret. */
object ProtocolNormalizationPass extends Transform with DependencyAPIMigration {
  // we need bundles and vectors to be lowered
  override def prerequisites = Seq(Dependency(firrtl.passes.LowerTypes))
  override def invalidates(a: Transform) = false

  // we must run before whens are removed
  override def optionalPrerequisiteOf = Seq(Dependency(firrtl.passes.ExpandWhens))

  override protected def execute(state: CircuitState): CircuitState = {
    val c = state.circuit.mapModule(onModule)

    println("Normalization")
    println(state.circuit.serialize)

    state.copy(circuit = c)
  }

  private def onModule(m: ir.DefModule): ir.DefModule = {
    m.mapStmt(onStmt)
  }

  private def onStmt(s: ir.Statement): ir.Statement = s match {
    case other => other
  }
}

object CheckStatementsPass extends Transform with DependencyAPIMigration {
  override def prerequisites = Forms.Resolved
  override def invalidates(a: Transform) = false
  override protected def execute(state: CircuitState): CircuitState = {
    state.circuit.foreachModule(m => m.foreachStmt(onStmt))
    // this is purely a checking transform which has no effect
    state
  }
  private val allowedStopRets = Set(ProtocolCompiler.StepFunctionCode, ProtocolCompiler.ForkFunctionCode)
  private def onStmt(s: ir.Statement): Unit = s match {
    case ir.DefWire(info, name, _) =>
      throw new ProtocolError(s"Cannot declare wire $name in protocol (${info.serialize}")
    case ir.DefInstance(info, name, module, _) =>
      throw new ProtocolError(s"Cannot declare instance $name of $module in protocol (${info.serialize}")
    case ir.DefMemory(info, name, _, _, _, _, _, _, _, _) =>
      throw new ProtocolError(s"Cannot declare memory $name in protocol (${info.serialize}")
    case ir.DefRegister(info, name, _, _, _, _) =>
      throw new ProtocolError(s"Cannot declare register $name in protocol (${info.serialize}")
    case ir.Attach(info, _) =>
      throw new ProtocolError(s"Cannot use analog signals in protocol (${info.serialize}")
    case ir.Print(info, _, _, _, _) =>
      throw new ProtocolError(s"Cannot use the print statement in protocol (${info.serialize}")
    case ir.Verification(ir.Formal.Assume, info, _, _, _, _) =>
      throw new ProtocolError(s"Cannot use the assume statement in protocol (might be worth considering though) (${info.serialize}")
    case ir.Verification(ir.Formal.Cover, info, _, _, _, _) =>
      throw new ProtocolError(s"Cannot use the cover statement in protocol (${info.serialize}")
    case ir.Stop(info, ret, _, _) if !allowedStopRets.contains(ret) =>
      throw new ProtocolError(s"Cannot use the stop statement in protocol (${info.serialize}")
    case other => other.foreachStmt(onStmt)
  }
}

class ProtocolError(s: String) extends PassException(s)
