package paso.chisel.passes

import firrtl.annotations.NoTargetAnnotation
import firrtl.{CircuitState, DependencyAPIMigration, Transform, ir}
import firrtl.options.Dependency

case class CrossModuleInput(name: String, portName: String, tpe: ir.Type) extends NoTargetAnnotation

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
    assert(main.ports.length == 2, f"Invariance modules should not have any ports besides clock and reset!")

    // find all cross module signals
    val signalsByPort = state.annotations.collect{ case a: CrossModuleInput => a }.groupBy(_.portName)

    // every circuit that is referenced gets their own port
    val newPorts = signalsByPort.map { case (portName, signals) =>
      val fields = signals.map(s => ir.Field(s.name, ir.Default, s.tpe))
      ir.Port(ir.NoInfo, portName, ir.Input, ir.BundleType(fields))
    }

    // check to make sure there is no aliasing
    val namespace = firrtl.Namespace(main)
    newPorts.foreach { p =>
      assert(!namespace.contains(p.name), f"Cannot create port ${p.name} because a signal of the same name already exists!")
    }

    // add new portsto main
    val newMain = main.copy(ports=main.ports ++ newPorts)

    state.copy(circuit = state.circuit.copy(modules = Seq(newMain)))
  }
}
