package paso.chisel.passes

import firrtl.analyses.InstanceKeyGraph
import firrtl.analyses.InstanceKeyGraph.InstanceKey
import firrtl.annotations.{CircuitTarget, InstanceTarget, ModuleTarget, ReferenceTarget, SingleTargetAnnotation}
import firrtl.options.Dependency
import firrtl.passes.InlineAnnotation
import firrtl.stage.Forms
import firrtl.transforms.DontTouchAnnotation
import firrtl.{AnnotationSeq, CircuitState, DependencyAPIMigration, Transform}

case class DoNotInlineAnnotation(target: ModuleTarget) extends SingleTargetAnnotation[ModuleTarget] {
  override def duplicate(n: ModuleTarget) = copy(target = n)
}

case class SubmoduleInstanceAnnotation(target: InstanceTarget, originalModule: String)
  extends SingleTargetAnnotation[InstanceTarget] {
  override def duplicate(n: InstanceTarget) = copy(target = n)
}

/** This pass deal with submodules in the implementation RTL:
 * - if no submodules are abstracted out, the complete hierarchy is inlined
 * - any submodule that needs to be abstracted is maintained and will eventually be exposed by the SMT backend
 * - we track the submodule instance name
 */
object PasoSubmoduleFlatten extends Transform with DependencyAPIMigration {
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

    // we need to keep track of the instance names of all non inlined submodules
    val submoduleAnnos = doNotInline.flatMap { name =>
      // find out where this module is instantiated
      val instances = iGraph.findInstancesInHierarchy(name)
      assert(instances.length == 1, "We expect there to be exactly one instance per module!")
      val instanceName = instances.head.last.name
      val parentModule = instances.head.dropRight(1).last.module

      val iRef = cRef.module(parentModule).instOf(instanceName, name)
      val instAnno = SubmoduleInstanceAnnotation(iRef, name)

      // we also want to insure that all I/O of the submodule is kept around
      val mRef = cRef.module(name)
      val dontTouchIO = iGraph.moduleMap(name).ports.map(p => DontTouchAnnotation(mRef.ref(p.name)))
      instAnno +: dontTouchIO
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