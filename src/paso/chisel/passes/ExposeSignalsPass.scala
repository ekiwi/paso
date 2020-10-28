// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel.passes

import firrtl.annotations.{CircuitTarget, NoTargetAnnotation, ReferenceTarget, SingleTargetAnnotation}
import firrtl.options.Dependency
import firrtl.passes.wiring.{SinkAnnotation, SourceAnnotation}
import firrtl.stage.Forms
import firrtl.{CircuitState, DependencyAPIMigration, Transform, ir}


/** requests a signal to be exposed */
case class SignalToExposeAnnotation(target: ReferenceTarget, name: String) extends SingleTargetAnnotation[ReferenceTarget] {
  override def duplicate(n: ReferenceTarget) = copy(target = n)
}
/** used to return the port name and the signal type */
case class ExposedSignalAnnotation(name: String, portName: String, tpe: ir.Type) extends NoTargetAnnotation

/** Exposes internal signals of the circuit as toplevel outputs. */
object ExposeSignalsPass extends Transform with DependencyAPIMigration {
  // We want to run this after type inference in order to get the proper port types, but before LowerTypes etc.
  override def prerequisites = Forms.Resolved
  // since we emit wiring annotations, we need to run before the wiring transform
  // we also want ot run before Dedup since dedup could screw up some of our paths which we copied from Chisel
  override def optionalPrerequisiteOf = Seq(Dependency[firrtl.transforms.DedupModules], Dependency[firrtl.passes.wiring.WiringTransform])
  override def invalidates(a: Transform): Boolean = a match {
    case firrtl.passes.ResolveKinds | firrtl.passes.ResolveFlows => true
    case _ => false
  }

  val DefaultPortName = "signals"

  override protected def execute(state: CircuitState): CircuitState = {
    val (annos, others) = state.annotations.partition(_.isInstanceOf[SignalToExposeAnnotation])
    // if there are no SignalToExposeAnnotations, this transform is a no-op
    if (annos.isEmpty) {
      state
    } else {
      val modules = state.circuit.modules.map(m => m.name -> m).toMap
      val main = modules(state.circuit.main).asInstanceOf[ir.Module]
      val signalPortName = firrtl.Namespace(main).newName(DefaultPortName)

      val signalPortRef = CircuitTarget(main.name).module(main.name).ref(signalPortName)
      val signalFieldsAndAnnos = annos.collect { case SignalToExposeAnnotation(signal, name) =>
        val tpe = findTpe(modules, signal)
        assert(tpe.isInstanceOf[ir.GroundType], f"Currently, only ground type references are supported. Not: ${tpe.serialize} of ${signal.serialize}")
        val field = ir.Field(name = name, flip = ir.Default, tpe = tpe)
        val src = SourceAnnotation(signal.toNamed, name)
        val sink = SinkAnnotation(signalPortRef.field(name).toNamed, name)
        val exposed = ExposedSignalAnnotation(name, signalPortName, tpe)
        (field, List(src, sink, exposed))
      }

      val signalPortTpe = ir.BundleType(signalFieldsAndAnnos.map(_._1))
      val signalPort = ir.Port(ir.NoInfo, name = signalPortName, direction = ir.Output, tpe = signalPortTpe)

      val wiringAnnos = signalFieldsAndAnnos.flatMap(_._2)

      // we need to add the new signalPort and invalidate it for now
      val newPorts = main.ports :+ signalPort
      val newBody = ir.Block(List(
        ir.IsInvalid(ir.NoInfo, ir.Reference(signalPortName, signalPortTpe)), main.body
      ))

      val newMain = main.copy(ports = newPorts, body = newBody)
      val newCircuit = state.circuit.copy(modules = state.circuit.modules.filterNot(_.name == main.name) ++ Seq(newMain))
      state.copy(circuit = newCircuit, annotations = others ++ wiringAnnos)
    }
  }

  private val symbolTables = scala.collection.mutable.HashMap[String, LocalSymbolTable]()

  private def findTpe(modules: Map[String, ir.DefModule], target: ReferenceTarget): ir.Type = {
    val symbols = symbolTables.getOrElseUpdate(target.module, {
      firrtl.analyses.SymbolTable.scanModule(modules(target.module), new LocalSymbolTable)
    })
    assert(target.component.isEmpty, "TODO: support field/index references")
    symbols.nameToType(target.ref)
  }
}

private class LocalSymbolTable extends firrtl.analyses.SymbolTable {
  def declareInstance(name: String, module: String): Unit = declare(name, ir.UnknownType, firrtl.InstanceKind)
  override def declare(d: ir.DefInstance): Unit = declare(d.name, d.tpe, firrtl.InstanceKind)
  override def declare(name: String, tpe: ir.Type, kind: firrtl.Kind): Unit = {
    if(kind == firrtl.MemKind) {
      val port = tpe.asInstanceOf[ir.BundleType].fields.head.tpe.asInstanceOf[ir.BundleType]
      val dataType = port.fields.find(_.name.endsWith("data")).map(_.tpe).get
      val addrType = port.fields.find(_.name.endsWith("addr")).map(_.tpe).get.asInstanceOf[ir.UIntType]
      throw new NotImplementedError(s"TODO: deal with memory kind! $name : ${addrType.serialize} -> ${dataType.serialize}")
    } else {
      nameToType(name) = tpe
    }
  }
  val nameToType = scala.collection.mutable.HashMap[String, ir.Type]()
}
