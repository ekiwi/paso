package paso.chisel.passes

import firrtl.{CircuitState, DependencyAPIMigration, Transform, ir}
import firrtl.options.Dependency

import scala.collection.mutable


/** Replace all references to signals outside of the module with input ports.
 *  This pass is used to elaborate invariants and mapping functions separately from
 *  the module that they are referring to.
 *
 *  @note Connecting to cross module references is *not* allowed!
 *
 * */
object CrossModuleReferencesToInputsPass extends Transform with DependencyAPIMigration {
  // We need to fix up the ports before any checks are run, so this pass runs as early as possible.
  override def prerequisites = Seq()
  override def optionalPrerequisiteOf = Seq(Dependency(firrtl.passes.CheckChirrtl))
  override def invalidates(a: Transform): Boolean = false

  override protected def execute(state: CircuitState): CircuitState = {
    assert(state.circuit.modules.length == 1, "We expect the invariants to be declared inside a single module!")
    val main = state.circuit.modules.find(_.name == state.circuit.main).get.asInstanceOf[ir.Module]
    val namespace = firrtl.Namespace(main)
    println(state.circuit.serialize)
    state
  }
}
