package paso.chisel.passes

import firrtl.annotations.{Annotation, CircuitTarget, ReferenceTarget, SingleTargetAnnotation}
import firrtl.{CircuitState, DependencyAPIMigration, Transform, ir}
import firrtl.options.Dependency
import firrtl.stage.Forms

import scala.collection.mutable

case class AssertPredicate(target: ReferenceTarget, msg: String) extends SingleTargetAnnotation[ReferenceTarget] {
  override def duplicate(n: ReferenceTarget) = copy(target = n)
}
case class AssertClock(target: ReferenceTarget, msg: String) extends SingleTargetAnnotation[ReferenceTarget] {
  override def duplicate(n: ReferenceTarget) = copy(target = n)
}
case class AssertEnable(target: ReferenceTarget, msg: String) extends SingleTargetAnnotation[ReferenceTarget] {
  override def duplicate(n: ReferenceTarget) = copy(target = n)
}

/** This pass converts all asserts statements to outputs.
 *  Currently this only works for a single main module, however, using the wiring pass one could
 *  enable this on a non-flat hierarchy.
 *
 */
class AssertsToOutputs extends Transform with DependencyAPIMigration {
  // We need to fix up the ports before any checks are run, so this pass runs as early as possible.
  override def prerequisites = Forms.LowForm
  override def invalidates(a: Transform): Boolean = false

  private val newAnnos = mutable.ArrayBuffer[Annotation]()
  private val newOutputs = mutable.ArrayBuffer[ir.Port]()
  private var namespace = firrtl.Namespace()
  private var mRef = CircuitTarget("").module("")

  override protected def execute(state: CircuitState): CircuitState = {
    assert(state.circuit.modules.length == 1, "We expect the invariants to be declared inside a single module!")
    val main = state.circuit.modules.find(_.name == state.circuit.main).get.asInstanceOf[ir.Module]
    namespace = firrtl.Namespace(main)
    mRef = CircuitTarget(main.name).module(main.name)

    val newBody = main.body.mapStmt(onStmt)
    val newMain = main.copy(body = newBody, ports = main.ports ++ newOutputs)

    state.copy(circuit = state.circuit.copy(modules = List(newMain)), annotations = state.annotations ++ newAnnos)
  }
  private def onStmt(s: ir.Statement): ir.Statement = s match {
    case ir.Verification(ir.Formal.Assert, info, clk, pred, en, msg) =>
      val connects = List(
        connectOut(info, "assert_en", en, name => AssertEnable(mRef.ref(name), msg.string)),
        connectOut(info, "assert_clk", clk, name => AssertClock(mRef.ref(name), msg.string)),
        connectOut(info, "assert_pred", pred, name => AssertPredicate(mRef.ref(name), msg.string))
      )
      ir.Block(connects)
    case other => other.mapStmt(onStmt)
  }

  private def connectOut(info: ir.Info, name: String, signal: ir.Expression, anno: String => Annotation): ir.Statement = {
    val port = ir.Port(info, namespace.newName(name), ir.Output, signal.tpe)
    newOutputs.append(port)
    newAnnos.append(anno(port.name))
    ir.Connect(info, ir.Reference(port.name, port.tpe, firrtl.PortKind, firrtl.SinkFlow), signal)
  }

}
