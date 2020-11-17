// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>


package paso.untimed

import firrtl.{AnnotationSeq, CircuitState, ir}
import firrtl.annotations._

import scala.collection.mutable

/** Replaces methods of annotated modules with connections to an ExtModule which can later be replaced with
 *  call to uninterpreted functions.
 *  - only works for module that do not have state (not even transitively)!
 *  */
object UninterpretedMethods {
  def run(state: CircuitState, abstracted: Iterable[AbstractModuleAnnotation]): CircuitState = {
    if(abstracted.isEmpty) { return state }

    // filter out duplicates for modules that need to be abstracted
    val nonDuplicateAbstracted = abstracted.groupBy(_.target.serialize).map { case (_, annos) =>
      val first = annos.head
      annos.tail.foreach(a => assert(a.prefix == first.prefix, s"Non matching prefix: ${a.prefix} != ${first.prefix}"))
      // we assume that module names uniquely identify instances (modules are not deduplicatd!)
      val mod = first.target match {
        case m: ModuleTarget => m.module
        case i: InstanceTarget => i.ofModule
      }
      mod -> first.prefix
    }.toMap
    val (newModules, mainInfo) = run(state.circuit.main, state, nonDuplicateAbstracted)
    val annos = state.annotations.filterNot(a => a.isInstanceOf[MethodIOAnnotation] || a.isInstanceOf[MethodCallAnnotation])
    val infoAnno = UntimedModuleInfoAnnotation(CircuitTarget(state.circuit.main).module(mainInfo.name), mainInfo)
    state.copy(circuit = state.circuit.copy(modules = newModules), annotations = annos :+ infoAnno)
  }


  /** replaces methods with calls to uninterpreted functions which are modelled as ExtModules */
  private def abstractMethods(mod: ir.Module, annos: AnnotationSeq, ufPrefix: String) = {
    // method are of the following general pattern:
    // ```
    // method.guard <= UInt<1>("h1")
    // method.ret is invalid
    // when method.enabled :
    //   ; method body
    // ```
    // we know all the method names, so we can just search for a Conditionally that checks the `method_name.enabled` signal
    val ioToName = annos.collect{ case a: MethodIOAnnotation if a.target.module == mod.name => a.target.ref -> a.name }.toMap

    val calls = mutable.ArrayBuffer[UFCallInfo]()

    def onStmt(s: ir.Statement): ir.Statement = s match {
      case c : ir.Conditionally => c.pred match {
        case ir.SubField(ir.Reference(ioName, _, _, _), "enabled", _, _) if ioToName.contains(ioName) =>
          assert(c.alt == ir.EmptyStmt)
          val (call, newBody) = abstractMethod(ioToName(ioName), ioName, ufPrefix, c.conseq)
          calls.append(call)
          // the guard will be moved into the method to solely guard the state updates
          c.copy(pred = ir.UIntLiteral(1), conseq = newBody)
        case _ => c // methods should not be enclosed in other when blocks!
      }
      case c : ir.Connect => c.loc match {
        // we only support abstracting methods for state-less modules, thus the guard should always be true!
        case ir.SubField(ir.Reference(ioName, _, _, _), "guard", _, _) if ioToName.contains(ioName) =>
          assert(c.expr match { case ir.UIntLiteral(v, _) if v == 1 => true case _ => false },
            s"Guard expected to be true, not: ${c.serialize}")
          c
        case _ => c
      }
      case other => other.mapStmt(onStmt)
    }
    val newMod = mod.mapStmt(onStmt).asInstanceOf[ir.Module]

    (calls.toSeq, newMod)
  }

  private def abstractMethod(parent: ModuleTarget, name: String, ioName: String, ufPrefix: String, body: ir.Statement): (UFCallInfo, ir.Statement) = {
    val argTarget = parent.ref(ioName).field("arg")
    val retTarget = parent.ref(ioName).field("ret")
    val functionName = ufPrefix + "." + name
    val anno = FunctionCallAnnotation(List(argTarget), List(retTarget), functionName)

    // find types
    var argTpe = ir.UIntType(ir.IntWidth(0))
    var retTpe = ir.UIntType(ir.IntWidth(0))

  }


}

case class AbstractModuleAnnotation(target: IsModule, prefix: String) extends SingleTargetAnnotation[IsModule] {
  override def duplicate(n: IsModule) = copy(target = n)
}

case class FunctionCallAnnotation(args: Seq[ReferenceTarget], rets: Seq[ReferenceTarget], name: String) extends MultiTargetAnnotation {
  override val targets = Seq(rets ++ args)
  override def duplicate(n: Seq[Seq[Target]]) = {
    assert(n.size == rets.size + args.size)
    val r = n.take(rets.size).flatten.map(_.asInstanceOf[ReferenceTarget])
    val a = n.drop(rets.size).flatten.map(_.asInstanceOf[ReferenceTarget])
    FunctionCallAnnotation(args=a, rets=r, name=name)
  }
}

case class UFCallInfo(anno: FunctionCallAnnotation, argTpe: ir.Type, retTpe: ir.Type)