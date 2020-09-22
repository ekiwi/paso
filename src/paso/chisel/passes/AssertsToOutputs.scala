package paso.chisel.passes

import firrtl.annotations.{Annotation, CircuitTarget, ReferenceTarget, SingleTargetAnnotation}
import firrtl.{CircuitState, DependencyAPIMigration, Transform, ir}
import firrtl.options.Dependency
import firrtl.stage.Forms

import scala.collection.mutable

case class AssertPredicate(target: ReferenceTarget, name: String, msg: String) extends SingleTargetAnnotation[ReferenceTarget] {
  override def duplicate(n: ReferenceTarget) = copy(target = n)
}
case class AssertEnable(target: ReferenceTarget, name: String, msg: String) extends SingleTargetAnnotation[ReferenceTarget] {
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
      val name = freshAssertPrefix
      val annos = List(AssertEnable(mRef.ref(name + "_en"), name, msg.string),
        AssertPredicate(mRef.ref(name + "_pred"), name, msg.string))
      newAnnos.append(annos:_*)
      val connects = List(connectOut(info, name, "_en", en), connectOut(info, name, "_pred", pred))
      ir.Block(connects)
    case other => other.mapStmt(onStmt)
  }

  private val suffixes = List("_en", "_pred", "_clk")
  // get a new assert output prefix
  private def freshAssertPrefix: String = {
    val name = Iterator.from(0).map(i => s"assert$i").find(name => suffixes.forall(s => !namespace.contains(s"$name$s"))).get
    suffixes.foreach(s => namespace.newName(s"$name$s"))
    name
  }

  private def connectOut(info: ir.Info, name: String, suffix: String, signal: ir.Expression): ir.Statement = {
    val port = ir.Port(info, name + suffix, ir.Output, signal.tpe)
    newOutputs.append(port)
    ir.Connect(info, ir.Reference(port.name, port.tpe, firrtl.PortKind, firrtl.SinkFlow), signal)
  }

}
