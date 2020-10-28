package paso.chisel.passes

import firrtl.{CircuitState, DependencyAPIMigration, Namespace, Transform, ir}
import firrtl.stage.Forms

/** This is a workaround for the following firrtl SMT backend issue:
 *  https://github.com/freechipsproject/firrtl/issues/1934
 *
 *  In this pass, we ensure that all asserts in the circuit have a unique message
 *  to make sure that they won't collide with any signal names.
 */
object UniqueVerificationMessagesPass extends Transform with DependencyAPIMigration {
  override def prerequisites = Forms.LowForm
  override def invalidates(a: Transform): Boolean = false

  override protected def execute(state: CircuitState): CircuitState = {
    val c = state.circuit.mapModule(onModule)
    state.copy(circuit = c)
  }

  private def onModule(m: ir.DefModule): ir.DefModule = m match {
    case e: ir.ExtModule => e
    case mod: ir.Module =>
      val namespace = Namespace(Seq(""))
      mod.copy(body = mod.body.mapStmt(onStmt(namespace)))
  }

  private def onStmt(namespace: Namespace)(s: ir.Statement): ir.Statement = s match {
    case v @ ir.Verification(_, _, _, _, _, msg) =>
      val newMsg = namespace.newName(msg.string)
      if(msg.string == newMsg) { v } else { v.copy(msg = ir.StringLit(newMsg)) }
    case other => other.mapStmt(onStmt(namespace))
  }
}
