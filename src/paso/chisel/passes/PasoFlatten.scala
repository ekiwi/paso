package paso.chisel.passes

import firrtl.analyses.InstanceKeyGraph
import firrtl.analyses.InstanceKeyGraph.InstanceKey
import firrtl.annotations.{CircuitTarget, ModuleTarget, ReferenceTarget, SingleTargetAnnotation}
import firrtl.options.Dependency
import firrtl.passes.InlineAnnotation
import firrtl.stage.Forms
import firrtl.{AnnotationSeq, CircuitState, DependencyAPIMigration, Transform}

case class DoNotInlineAnnotation(target: ModuleTarget) extends SingleTargetAnnotation[ModuleTarget] {
  override def duplicate(n: ModuleTarget) = copy(target = n)
}

case class SubmoduleIOAnnotation(target: ReferenceTarget) extends SingleTargetAnnotation[ReferenceTarget] {
  override def duplicate(n: ReferenceTarget) = copy(target = n)
}

object PasoFlatten extends Transform with DependencyAPIMigration {
  override def prerequisites = Forms.WorkingIR
  // this pass relies on modules not being dedupped
  override def optionalPrerequisiteOf = Seq(Dependency[firrtl.transforms.DedupModules])

  override protected def execute(state: CircuitState): CircuitState = {
    val doNotInline = state.annotations
      .collect{ case DoNotInlineAnnotation(target) if target.circuit == state.circuit.main => target.module }
    val iGraph = InstanceKeyGraph(state.circuit)
    val children = iGraph.getChildInstances.toMap

    // we tag every module to be inlined unless it is explicitly marked as doNotInline
    val cRef = CircuitTarget(state.circuit.main)
    val main = cRef.module(state.circuit.main)
    val inlineAnnos = inlines(main)(children, doNotInline.toSet)

    // we need to keep track of the IO of all non-inlined modules
    val submoduleAnnos = doNotInline.flatMap { name =>
      val mRef = cRef.module(name)
      iGraph.moduleMap(name).ports.map(p => mRef.ref(p.name)).map(SubmoduleIOAnnotation)
    }

    val annos = state.annotations.filterNot(_.isInstanceOf[DoNotInlineAnnotation]) ++ inlineAnnos ++ submoduleAnnos
    state.copy(annotations = annos)
  }

  private def inlines(m: ModuleTarget)(implicit children: Map[String, Seq[InstanceKey]], doNotInline: Set[String]): AnnotationSeq = {
    if(doNotInline.contains(m.module)) { Seq() } else {
      InlineAnnotation(m) +: children(m.module).flatMap(c => inlines(m.targetParent.module(c.module)))
    }
  }
}