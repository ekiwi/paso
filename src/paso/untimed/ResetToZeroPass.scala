// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.untimed

import firrtl.annotations.{Annotation, CircuitTarget, MemoryInitAnnotation, MemoryScalarInitAnnotation, ModuleTarget, ReferenceTarget}
import firrtl.options.Dependency
import firrtl.{AnnotationSeq, CircuitState, DependencyAPIMigration, Transform, ir}

import scala.collection.mutable

/** Adds a default reset value of zero to all registers and memories that do not have a reset. */
object ResetToZeroPass extends Transform with DependencyAPIMigration {
  // we run on after LowerTypes b/c it is easier to calculate a reset for ground types
  override def prerequisites = Seq(Dependency(firrtl.passes.LowerTypes))
  // we need to run before RemoveReset because we need to know if the register already has a reset value specified
  override def optionalPrerequisiteOf = Seq(Dependency(firrtl.transforms.RemoveReset))
  override def invalidates(a: Transform): Boolean = false

  override protected def execute(state: CircuitState) = {
    val mems = mutable.ArrayBuffer[ReferenceTarget]()
    val cRef = CircuitTarget(state.circuit.main)
    val c = state.circuit.mapModule(onModule(_, cRef, mems))
    val annos = initMems(mems, state.annotations)
    state.copy(circuit = c, annotations = state.annotations ++ annos)
  }

  private def initMems(mems: Iterable[ReferenceTarget], annos: AnnotationSeq): AnnotationSeq = {
    // make a list of memories that are initialized by the user
    val initialized = annos.collect{ case a : MemoryInitAnnotation => a.target }.toSet
    mems.collect { case m if !initialized.contains(m) => MemoryScalarInitAnnotation(m, 0) }.toSeq
  }

  private def onModule(m: ir.DefModule, c: CircuitTarget, mems: mutable.ArrayBuffer[ReferenceTarget]): ir.DefModule = {
    m.mapStmt(onStmt(_, c.module(m.name), mems))
  }

  private val resetRef = ir.Reference("reset", ir.AsyncResetType, firrtl.PortKind, firrtl.SourceFlow)

  private def onStmt(s: ir.Statement, m: ModuleTarget, mems: mutable.ArrayBuffer[ReferenceTarget]): ir.Statement = s match {
    case r : ir.DefRegister =>
      r.init match {
        case ir.Reference(name, _, _, _) if name == r.name =>
          val zero = r.tpe match {
            case ir.UIntType(w) => ir.UIntLiteral(0, w)
            case ir.SIntType(w) => ir.SIntLiteral(0, w)
            case other => throw new RuntimeException(s"Unexpected register type: ${other.serialize}")
          }
          // registers without a reset might not be connected to the reset port, we fix that
          r.copy(init=zero, reset = resetRef)
        case _ => r
      }
    case mem : ir.DefMemory => mems.append(m.ref(mem.name)) ; mem
    case other => other.mapStmt(onStmt(_, m, mems))
  }
}
