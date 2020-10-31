// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel.passes

import firrtl.annotations.{NoTargetAnnotation, ReferenceTarget, SingleTargetAnnotation}
import firrtl.{CircuitState, DependencyAPIMigration, Transform, ir}
import firrtl.options.Dependency

case class CrossModuleInput(target: ReferenceTarget, tpe: ir.Type) extends SingleTargetAnnotation[ReferenceTarget] {
  override def duplicate(n: ReferenceTarget) = copy(target = n)
}

case class CrossModuleMem(target: ReferenceTarget, depth: BigInt, dataTpe: ir.Type) extends SingleTargetAnnotation[ReferenceTarget] {
  override def duplicate(n: ReferenceTarget) = copy(target = n)
}

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

    // all signals besides memories result in an input port
    val newPorts = state.annotations.collect { case a: CrossModuleInput =>
      assert(a.target.circuit == state.circuit.main)
      assert(a.target.module == main.name)
      ir.Port(ir.FileInfo("observed external signal"), a.target.ref, ir.Input, a.tpe)
    }

    // memories result in a local copy of the memory
    val mems = state.annotations.collect { case a: CrossModuleMem =>
      assert(a.target.circuit == state.circuit.main)
      assert(a.target.module == main.name)
      firrtl.CDefMemory(ir.FileInfo("observed external signal"), a.target.ref, a.dataTpe, a.depth,
        seq=false, readUnderWrite = ir.ReadUnderWrite.Undefined)
    }

    // add new ports to main
    val newMain = main.copy(ports=main.ports ++ newPorts, body = ir.Block(mems :+ main.body))

    state.copy(circuit = state.circuit.copy(modules = Seq(newMain)))
  }
}
