// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel.passes

import firrtl._
import firrtl.stage.Forms

object InvertAssertPass extends Transform with DependencyAPIMigration {
  override def prerequisites = Forms.LowForm
  override def invalidates(a: Transform): Boolean = false

  val DefaultPortName = "invertAssert"

  override protected def execute(state: CircuitState): CircuitState = {
    assert(state.circuit.modules.length == 1, "No support for sub modules!")
    val c = state.circuit.mapModule(onModule)
    state.copy(circuit = c)
  }

  private val Bool = ir.UIntType(ir.IntWidth(1))
  private def onModule(m: ir.DefModule): ir.DefModule = {
    val mod = m.asInstanceOf[ir.Module]
    val namespace = Namespace(mod)
    val portName = namespace.newName(DefaultPortName)
    val port = ir.Port(ir.NoInfo, portName, ir.Input, Bool)
    val doAssumeNode = ir.DefNode(ir.NoInfo, namespace.newName("doAssume"),
      ir.Reference(portName, Bool, firrtl.PortKind, firrtl.SourceFlow))
    val doAssume = ir.Reference(doAssumeNode)
    val doAssertNode = ir.DefNode(ir.NoInfo, namespace.newName("doAssert"), Utils.not(doAssume))
    val doAssert = ir.Reference(doAssertNode)
    val b = Seq(doAssumeNode, doAssertNode) :+ mod.body.mapStmt(onStmt(doAssume, doAssert, namespace))
    val p = mod.ports :+ port
    mod.copy(ports=p, body=ir.Block(b))
  }

  private def onStmt(doAssume: ir.Expression, doAssert: ir.Expression, namespace: Namespace)(s: ir.Statement): ir.Statement = s match {
    case a @ ir.Verification(ir.Formal.Assert, info, _, pred, en, _) =>
      val predNode = ir.DefNode(info, namespace.newName("_GEN_assert_pred"), pred)
      val predRef = ir.Reference(predNode)
      val enNode = ir.DefNode(info, namespace.newName("_GEN_assert_en"), en)
      val enRef = ir.Reference(enNode)
      val assertion = ir.Verification(ir.Formal.Assert, a.info, a.clk,
        pred=predRef, en=Utils.and(doAssert, enRef), msg=a.msg, name=a.name)
      val assumption = ir.Verification(ir.Formal.Assume, a.info, a.clk,
        pred=predRef, en=Utils.and(doAssume, enRef), msg=a.msg,
        name=namespace.newName(a.name + "_assume"))
      ir.Block(List(predNode, enNode, assertion, assumption))
    case other => other.mapStmt(onStmt(doAssume, doAssert, namespace))
  }

}