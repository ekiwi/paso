// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>


package paso.untimed

import firrtl.analyses.InstanceKeyGraph
import firrtl.analyses.InstanceKeyGraph.InstanceKey
import firrtl.{AnnotationSeq, CircuitState, Namespace, ir}
import firrtl.annotations._
import maltese.mc
import maltese.smt
import paso.verification.TopologicalSort

import scala.collection.mutable

/** Replaces methods of annotated modules with connections to an ExtModule which can later be replaced with
 *  call to uninterpreted functions.
 *  - only works for module that do not have state (not even transitively)!
 *  */
object UninterpretedMethods {

  /** adds UFs to replace connections to function call modules, use after generating transitions system */
  def connectUFs(sys: mc.TransitionSystem, annos: AnnotationSeq, prefix: String): mc.TransitionSystem = {
    val calls = annos.collect{ case a: FunctionCallAnnotation => a }
    if(calls.isEmpty) { return sys }

    val cons = calls.flatMap { c =>
      val isArg = c.args.map(toName).map(prefix + _).toSet
      val argSymbols = sys.signals.filter(s => isArg(s.name)).map(_.toSymbol)
      assert(c.args.length == argSymbols.length, s"Missing arguments! ${c.args} vs. ${argSymbols}\n${sys.serialize}")

      val isRet = c.rets.map(toName).map(prefix + _).toSet
      val retSymbols = sys.inputs.filter(s => isRet(s.name))
      assert(c.rets.length == retSymbols.length, s"Missing arguments! ${c.rets} vs. ${retSymbols}\n${sys.serialize}")

      c.rets.zip(retSymbols).map { case (r, sym) =>
        sym.name -> smt.BVFunctionCall(c.name + "." + r.ref, argSymbols, sym.width)
      }
    }

    val connectedSys = mc.TransitionSystem.connect(sys, cons.toMap)

    // because the inputs are connected to internal (output) signals through the UF, we need to resort the system
    val sortedSys = TopologicalSort.run(connectedSys)

    sortedSys
  }

  private def toName(target: ReferenceTarget): String = {
    val path = target.module +: target.path.map(_._1.value) :+ target.ref
    assert(target.component.isEmpty, "TODO: deal with non empty component!")
    path.mkString(".")
  }


  def run(state: CircuitState, abstracted: Iterable[AbstractModuleAnnotation]): CircuitState = {
    if(abstracted.isEmpty) { return state }

    // filter out duplicates for modules that need to be abstracted
    val nonDuplicateAbstracted = abstracted.groupBy(_.target.serialize).map { case (_, annos) =>
      val first = annos.head
      annos.tail.foreach(a => assert(a.prefix == first.prefix, s"Non matching prefix: ${a.prefix} != ${first.prefix}"))
      // we assume that module names uniquely identify instances (modules are not deduplicatd!)
      first.target -> first.prefix
    }.toMap

    // find modules to be abstracted and replace their method implementations
    val main = CircuitTarget(state.circuit.main).module(state.circuit.main)
    val callMap = new CallMap()
    val (changedModules, calls) = run(main, state, callMap, nonDuplicateAbstracted)

    // add ExtModule
    val newModules = changedModules ++ callMap.values

    state.copy(circuit = state.circuit.copy(modules = newModules), annotations = state.annotations ++ calls)
  }

  private def get(target: IsModule, state: CircuitState): ir.DefModule = {
    val name = moduleName(target)
    state.circuit.modules.find(_.name == name).get
  }

  private def moduleName(target: IsModule): String = {
    target match {
      case m: ModuleTarget => m.module
      case i: InstanceTarget => i.ofModule
    }
  }

  /** Visit modules top down through the hierarchy to check if they need to be abstracted. */
  private def run(target: IsModule, state: CircuitState, map: CallMap, abstracted: Map[IsModule, String]): (Seq[ir.DefModule], AnnotationSeq) = {
    abstracted.get(target) match {
      case Some(prefix) => abstractModule(target, state, map, prefix)
      case None =>
        val mod = get(target, state)
        // find all submodules and check if they are abstract
        val submodules = InstanceKeyGraph.collectInstances(mod)
        val r = submodules.map(i => run(target.instOf(i.name, i.module), state, map, abstracted))
        val modules = r.flatMap(_._1) :+ mod
        (modules, r.flatMap(_._2))
    }
  }

  private def abstractModule(target: IsModule, state: CircuitState, map: CallMap, prefix: String): (Seq[ir.Module], AnnotationSeq) = {
    val mod = get(target, state).asInstanceOf[ir.Module]
    // we need to ensure that this module has no state since abstraction is only supported for state-less modules
    assert(!hasState(mod), f"$target: Only state-less modules can be abstracted!")

    // remove all submodules as they will no longer be needed
    val (_, modWithoutInstances) = ConnectCalls.removeInstances(mod, _ => false)

    // find method types and determine ext module names
    val namespace = Namespace(mod)
    val methods = state.annotations.collect{ case a: MethodIOAnnotation if a.target.module == mod.name => a }.map { m =>
      val ioName = m.target.ref
      val functionName = prefix + "." + m.name
      val methodIO = mod.ports.find(_.name == ioName).get
      val argTpe = methodIO.tpe.asInstanceOf[ir.BundleType].fields.find(_.name == "arg").get.tpe
      val retTpe = methodIO.tpe.asInstanceOf[ir.BundleType].fields.find(_.name == "ret").get.tpe
      val extModule = getFunctionModule(map, functionName, argTpe, retTpe)
      val instanceName = namespace.newName(m.name + "_ext")
      // we annotate the ports of the ext module instance b/c these will be exposed by the firrtl backend
      val argTarget = target.instOf(instanceName, extModule).ref("arg")
      val retTarget = target.instOf(instanceName, extModule).ref("ret")
      val anno = FunctionCallAnnotation(List(argTarget), List(retTarget), functionName)
      MInfo(m.name, anno, ioName, argTpe, retTpe, functionName, instanceName, extModule)
    }

    // change method bodies to use ExtModules
    val newBodies = abstractMethods(mod, methods)

    // filter out ports that do not belong to methods (this is trying to get rid of port for calls to submodules
    val allowedPorts = Set("reset", "clock") ++ methods.map(_.ioName)
    val filteredPorts = newBodies.ports.filter(p => allowedPorts(p.name))

    (List(newBodies.copy(ports = filteredPorts)), methods.map(_.anno))
  }

  private case class MInfo(name: String, anno: FunctionCallAnnotation, ioName: String, argTpe: ir.Type, retTpe: ir.Type,
    functionName: String, instanceName: String, extName: String)

  private def hasState(mod: ir.DefModule): Boolean = mod match {
    case _: ir.ExtModule => false
    case m: ir.Module =>
      println("TODO: implement hasState in UninterpretedMethods")
      false
  }


  /** replaces methods with calls to uninterpreted functions which are modelled as ExtModules */
  private def abstractMethods(mod: ir.Module, infos: Iterable[MInfo]): ir.Module = {
    // method are of the following general pattern:
    // ```
    // method.guard <= UInt<1>("h1")
    // method.ret is invalid
    // when method.enabled :
    //   ; method body
    // ```

    val ioNames = infos.map(m => m.ioName -> m).toMap

    def onStmt(s: ir.Statement): ir.Statement = s match {
      case c : ir.Conditionally => c.pred match {
        case ir.SubField(ir.Reference(ioName, _, _, _), "enabled", _, _) if ioNames.contains(ioName) =>
          assert(c.alt == ir.EmptyStmt)
          val m = ioNames(ioName)
          val newBody = ir.Block(List(
            // connect inputs first
            ir.Connect(ir.NoInfo, ir.SubField(ir.Reference(m.instanceName), "arg"), ir.SubField(ir.Reference(ioName), "arg")),
            // outputs second in order to maintain data flow order
            ir.Connect(ir.NoInfo, ir.SubField(ir.Reference(ioName), "ret"), ir.SubField(ir.Reference(m.instanceName), "ret")),
          ))
          c.copy(conseq = newBody)
        case _ => c // methods should not be enclosed in other when blocks!
      }
      case c : ir.Connect => c.loc match {
        // we only support abstracting methods for state-less modules, thus the guard should always be true!
        case ir.SubField(ir.Reference(ioName, _, _, _), "guard", _, _) if ioNames.contains(ioName) =>
          assert(c.expr match { case ir.UIntLiteral(v, _) if v == 1 => true case _ => false },
            s"Guard expected to be true, not: ${c.serialize}")
          c
        case _ => c
      }
      case other => other.mapStmt(onStmt)
    }
    val newBody = mod.body.mapStmt(onStmt)
    val instances = infos.flatMap{ m => List(
      ir.DefInstance(m.instanceName, m.extName),
      ir.IsInvalid(ir.NoInfo, ir.SubField(ir.Reference(m.instanceName), "arg"))
    )}

    mod.copy(body = ir.Block(instances.toList :+ newBody))
  }

  private type CallMap = mutable.HashMap[String, ir.ExtModule]
  private def getFunctionModule(map: CallMap, name: String, argTpe: ir.Type, retTpe: ir.Type): String = {
    val mod = map.getOrElseUpdate(name, {
      val namespace = Namespace(map.values.map(_.name).toSeq)
      val modName = namespace.newName(name.replace('.', '_'))
      val ports = List(ir.Port(ir.NoInfo, "arg", ir.Input, argTpe), ir.Port(ir.NoInfo, "ret", ir.Output, retTpe))
      ir.ExtModule(ir.NoInfo, name = modName, ports=ports, defname=name, Seq())
    })
    assert(mod.defname == name)
    assert(mod.ports.find(_.name == "arg").exists(_.tpe == argTpe))
    assert(mod.ports.find(_.name == "ret").exists(_.tpe == retTpe))
    mod.name
  }

}

case class AbstractModuleAnnotation(target: IsModule, prefix: String) extends SingleTargetAnnotation[IsModule] {
  override def duplicate(n: IsModule) = copy(target = n)
}

case class FunctionCallAnnotation(args: Seq[ReferenceTarget], rets: Seq[ReferenceTarget], name: String) extends MultiTargetAnnotation {
  override val targets = List(rets, args)
  override def duplicate(n: Seq[Seq[Target]]) = {
    assert(n.size == 2)
    val r = n.head.map(_.asInstanceOf[ReferenceTarget])
    val a = n(1).map(_.asInstanceOf[ReferenceTarget])
    FunctionCallAnnotation(args=a, rets=r, name=name)
  }
}