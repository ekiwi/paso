// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.untimed

import firrtl.{AnnotationSeq, CircuitState, MInfer, MRead, MReadWrite, MWrite, Namespace, PrimOps, ir}
import firrtl.analyses.InstanceKeyGraph.InstanceKey
import firrtl.annotations.{CircuitTarget, InstanceTarget, IsModule, ModuleTarget, MultiTargetAnnotation, ReferenceTarget, SingleTargetAnnotation, Target}
import firrtl.ir.IntWidth
import firrtl.passes.PassException
import firrtl.stage.FirrtlCircuitAnnotation
import paso.chisel.FirrtlCompiler
import treadle.TreadleTester

import scala.collection.mutable

case class MethodInfo(name: String, parent: String, ioName: String, writes: Set[String], calls: Seq[CallInfo], args: Seq[(String, Int)] = List(), ret: Seq[(String, Int)] = List()) {
  def fullName: String = s"$parent.$name"
  def fullIoName: String = s"$parent.$ioName"
}
case class CallInfo(parent: String, method: String, ioName: String, info: ir.Info)
case class UntimedModuleInfo(name: String, state: Seq[ir.Reference], methods: Seq[MethodInfo], submodules: Seq[UntimedModuleInfo]) {
  val hasState: Boolean = state.nonEmpty || (submodules.count(_.hasState) > 0)
}

case class UntimedModuleInfoAnnotation(target: ModuleTarget, module: UntimedModuleInfo) extends SingleTargetAnnotation[ModuleTarget] {
  override def duplicate(n: ModuleTarget) = copy(target = n)
}

object UntimedCompiler {
  def run(state: CircuitState, abstracted: Iterable[AbstractModuleAnnotation] = List()): CircuitState = {
    val afterAbstraction = if(abstracted.nonEmpty) { UninterpretedMethods.run(state, abstracted) } else { state }
    val fixedCalls = ConnectCalls.run(afterAbstraction)
    // TODO: make ResetToZeroPass part of the firrtl compiler
    ResetToZeroPass.runTransform(FirrtlCompiler.toLowFirrtl(fixedCalls))
  }
  def toTreadleTester(chirrtl: CircuitState): TreadleTester = {
    val low = run(chirrtl, Set())
    val lowCircuit = FirrtlCircuitAnnotation(low.circuit)
    val treadleAst = prepareAst.transform(Seq(lowCircuit))
    new TreadleTester(treadleAst)
  }
  private val prepareAst = new treadle.stage.phases.PrepareAst()
}

/** Runs on the high firrtl representation of the untimed module circuit.
 *  Collects all calls to submodules, integrates them into guards, initializes method call wires
 *  properly and creates the call graph.
 * */
object ConnectCalls {

  def run(state: CircuitState): CircuitState = {
    val extMods = state.circuit.modules.collect { case m: ir.ExtModule => m }
    val (newModules, mainInfo) = run(state.circuit.main, state, extMods.map(_.name).toSet)
    val annos = state.annotations.filterNot(a => a.isInstanceOf[MethodIOAnnotation] || a.isInstanceOf[MethodCallAnnotation])
    val infoAnno = UntimedModuleInfoAnnotation(CircuitTarget(state.circuit.main).module(mainInfo.name), mainInfo)
    state.copy(circuit = state.circuit.copy(modules = newModules ++ extMods), annotations = annos :+ infoAnno)
  }

  private def run(name: String, state: CircuitState, isExt: String => Boolean): (Seq[ir.Module], UntimedModuleInfo) = {
    val mod = state.circuit.modules.collectFirst{ case m: ir.Module if m.name == name => m }.getOrElse(
      throw new RuntimeException(s"Could not find $name! ${state.circuit.modules.map(_.name)}")
    )
    val calls = state.annotations.collect { case  a: MethodCallAnnotation if a.callIO.module == mod.name => a}

    // analyze submodules first
    val (instances, mod1) = removeInstances(mod, isExt)
    val submods = instances.map(s => run(s.module, state, isExt))

    // collect metadata: state (regs + mems)
    val localState = findState(mod1)

    // analyze methods
    val (methods, mod2) = analyzeMethods(mod1, calls, state.annotations, localState.map(_.name).toSet)
    val info = UntimedModuleInfo(name, localState, methods, submods.map(_._2))

    // verify that all method calls are correct
    val nameToModule = info.submodules.map(s => s.name -> s).toMap
    verifyMethodCalls(name, methods, nameToModule)

    // connect submodules and instantiate them correctly
    val namespace = Namespace(mod) // important: make a namespace of the original module in order to include the original instance name
    val mod3 = connectSubmodules(namespace, mod2, info, instances, methods, nameToModule, calls)

    // ensure that only when a single method is enabled can its state be updated
    val newMod = exclusiveStateUpdates(namespace, mod3, info)

    (submods.flatMap(_._1) :+ newMod, info)
  }

  private def exclusiveStateUpdates(namespace: Namespace, mod: ir.Module, info: UntimedModuleInfo): ir.Module = {
    // a method is enabled iff its enable signal is high while all other enable signals are low
    def en(m: MethodInfo): ir.SubField = ir.SubField(ir.Reference(m.ioName), "enabled")
    def not(e: ir.Expression): ir.Expression = ir.DoPrim(PrimOps.Not, List(e), List(), ir.UnknownType)
    def and(a: ir.Expression, b: ir.Expression): ir.Expression = ir.DoPrim(PrimOps.And, List(a, b), List(), ir.UnknownType)
    val enabledNodes = info.methods.map { m =>
      val name = namespace.newName(m.name + "_enabled")
      val conds = info.methods.map(m2 => if(m2.name == m.name) { en(m2) } else { not(en(m2)) })
      ir.DefNode(ir.NoInfo, name, conds.reduce(and))
    }

    // replace references to method enables with their internal signal
    val enMap = info.methods.zip(enabledNodes).map{ case (m, n) => m.name -> n.name }.toMap
    val replaced = mod.mapStmt(replaceEnabled(_, enMap)).asInstanceOf[ir.Module]

    val newBody = ir.Block(enabledNodes :+ replaced.body)
    replaced.copy(body = newBody)
  }

  private def replaceEnabled(s: ir.Statement, enMap: Map[String, String]): ir.Statement =
    s.mapExpr(replaceEnabled(_, enMap)).mapStmt(replaceEnabled(_, enMap))
  private def replaceEnabled(e: ir.Expression, enMap: Map[String, String]): ir.Expression = e match {
    case ir.SubField(ir.Reference(name, _, _, _), "enabled", _, _) if enMap.contains(name) =>
      ir.Reference(enMap(name))
    case other => other.mapExpr(replaceEnabled(_, enMap))
  }

  private def connectSubmodules(namespace: Namespace, mod2: ir.Module, info: UntimedModuleInfo,
    instances: Seq[InstanceKey], methods: Seq[MethodInfo], nameToModule: Map[String, UntimedModuleInfo],
    calls: Iterable[MethodCallAnnotation]): ir.Module = {
    // calculate the number of instances for each submodule
    val finalInstances = info.submodules.flatMap { s =>
      val instanceName = instances.find(_.module == s.name).map(_.name).get
      // stateful modules only ever have a single instance since we need one "true" copy of the state
      if(s.hasState) {
        Some(s.name -> List(instanceName))
      } else {
        // find the max number of calls to any method of this module in a single method
        val maxCalls = methods.flatMap(m => m.calls.filter(_.parent == s.name).groupBy(_.method).map(_._2.size)).max
        // if this module is never called
        if(maxCalls == 0) { None } else {
          val copies = (0 until (maxCalls - 1)).map(_ => namespace.newName(instanceName))
          Some(s.name -> (List(instanceName) ++ copies))
        }
      }
    }.toMap

    // statements to declare instances and connect their reset and clock and inputs
    val instanceStatements = finalInstances.flatMap{ case (module, is) =>
      is.flatMap(i => makeInstance(i, module, nameToModule(module).methods.map(_.name)))
    }

    // connect calls to instances
    val connectCalls = methods.flatMap { meth =>
      val callCount = mutable.HashMap[String, Int]()
      meth.calls.map { call =>
        val fullName = s"${call.parent}.${call.method}"
        val count = callCount.getOrElseUpdate(fullName, 0)
        callCount(fullName) += 1
        val instance = finalInstances(call.parent)(count)
        // connect to instance
        val stmts = connectCallToInstanceAndDefaults(call, instance, call.info)
        ((instance -> call), stmts)
      }
    }
    val instanceToCall = connectCalls.map(_._1).groupBy(_._1)
    val connectCallStmts = connectCalls.flatMap(_._2)

    // connect the enabled and arg input of submodule methods
    // this requires an OR for enabled and a MUX for the arg
    val connectMethodInputs = instanceToCall.flatMap { case (instance, cc) =>
      assert(cc.nonEmpty)
      cc.map(_._2).groupBy(_.method).flatMap { case (method, calls) =>
        val enabled = calls.map(c => ir.SubField(ir.Reference(c.ioName), "enabled"))
          .reduce[ir.Expression]((a,b) => ir.DoPrim(PrimOps.Or, Seq(a,b), Seq(), ir.UnknownType))
        val info = ir.MultiInfo(calls.map(_.info).toSeq)
        val conEnabled = ir.Connect(info, ir.SubField(ir.SubField(ir.Reference(instance), method), "enabled"), enabled)
        val args = calls.map { c =>
          val con = ir.Connect(c.info, ir.SubField(ir.SubField(ir.Reference(instance), method), "arg"), ir.SubField(ir.Reference(c.ioName), "arg"))
          ir.Conditionally(c.info, ir.SubField(ir.Reference(c.ioName), "enabled"), con, ir.EmptyStmt)
        }
        args :+ conEnabled
      }
    }


    // demote call io to wires
    val (callPorts, nonCallPorts) = mod2.ports.partition(p => calls.exists(_.callIO.ref == p.name))
    val callIOWires = callPorts.map(p => ir.DefWire(p.info, p.name, p.tpe))

    val body = ir.Block((callIOWires ++ instanceStatements ++ connectCallStmts ++ connectMethodInputs ++ List(mod2.body)).toSeq)
    mod2.copy(body=body, ports = nonCallPorts)
  }

  private def connectCallToInstanceAndDefaults(call: CallInfo, instanceName: String, info: ir.Info = ir.NoInfo): List[ir.Statement] = List(
    // by default the call is disabled and the arg is DontCare
    ir.Connect(info, ir.SubField(ir.Reference(call.ioName), "enabled"), ir.UIntLiteral(0, IntWidth(1))),
    ir.IsInvalid(info, ir.SubField(ir.Reference(call.ioName), "arg")),
    // connect method ret and guard to call io
    ir.Connect(info, ir.SubField(ir.Reference(call.ioName), "ret"), ir.SubField(ir.SubField(ir.Reference(instanceName), call.method), "ret")),
    ir.Connect(info, ir.SubField(ir.Reference(call.ioName), "guard"), ir.SubField(ir.SubField(ir.Reference(instanceName), call.method), "guard")),
  )


  private def makeInstance(name: String, module: String, methods: Iterable[String], info: ir.Info = ir.NoInfo): List[ir.Statement] = List(
    ir.DefInstance(info, name, module),
    ir.Connect(info, ir.SubField(ir.Reference(name), "reset"), ir.Reference("reset")),
    ir.Connect(info, ir.SubField(ir.Reference(name), "clock"), ir.Reference("clock"))
  ) ++ methods.flatMap { method =>
    List(
      // by default a method is disabled (this is important in case it is never called!)
      ir.Connect(info, ir.SubField(ir.SubField(ir.Reference(name), method), "enabled"), ir.UIntLiteral(0, IntWidth(1))),
      // by default a method input is don't care
      ir.IsInvalid(info, ir.SubField(ir.SubField(ir.Reference(name), method), "arg")),
    )
  }

  private def verifyMethodCalls(name: String, methods: Iterable[MethodInfo], nameToModule: Map[String, UntimedModuleInfo]): Unit = {
    methods.foreach { m =>
      val callsByParent = m.calls.groupBy(_.parent)
      callsByParent.foreach { case (parent, calls) =>
        if(parent == name) {
          if(calls.map(_.method).contains(m.name)) {
            throw new UntimedError(s"[$name.${m.name}] recursive calls are not allowed!")
          } else {
            val cs = "Detected calls: " + calls.map(_.method).mkString(", ")
            throw new UntimedError(s"[$name.${m.name}] currently, only calls to submodules are supported!\n$cs")
          }
        }
        assert(nameToModule.contains(parent), s"$parent is not a submodule of $name!")
        val parentMod = nameToModule(parent)
        if(parentMod.hasState) {
          // if the submodule is stateful, we can only call one method
          if(calls.size > 1) {
            val cs = "Detected calls: " + calls.map(_.method).mkString(", ")
            throw new UntimedError(s"[$name.${m.name}] cannot call more than one method of stateful submodule $parent.\n$cs")
          }
        } // if the submodule is not stateful, we can call as many methods as we want to!
      }
    }
  }

  def removeInstances(m: ir.Module, doIgnore: String => Boolean): (Seq[InstanceKey], ir.Module) = {
    val instances = mutable.ArrayBuffer[InstanceKey]()

    def onStmt(s: ir.Statement): ir.Statement = s match {
      case ir.DefInstance(_, name, module, _) if !doIgnore(module) =>
        // remove the instance definition
        instances += InstanceKey(name, module) ; ir.EmptyStmt
      case _: firrtl.WDefInstanceConnector =>
        firrtl.Utils.throwInternalError("Expecting WDefInstance, found a WDefInstanceConnector!")
      case c @ ir.Connect(_, loc, _) =>
        // remove the connections to the instance clock and reset
        val locString = loc.serialize
        val toInstance = instances.exists(i => locString.startsWith(i.name + "."))
        if(toInstance) ir.EmptyStmt else c
      case other => other.mapStmt(onStmt)
    }

    val newM = m.copy(body=onStmt(m.body))
    (instances.toSeq, newM)
  }


  private val useMem = "you need to use a combinatorial Mem instead."
  def findState(mod: ir.Module): Seq[ir.Reference] = {
    val state = mutable.ArrayBuffer[ir.Reference]()

    def onStmt(s: ir.Statement): Unit = s match {
      case r : ir.DefRegister => state.append(ir.Reference(r.name, r.tpe))
      case m : ir.DefMemory =>
        if(m.readLatency > 0) {
          throw new UntimedError(s"[${mod.name}] memory ${m.name} has read latency ${m.readLatency} > 0. $useMem")
        }
        val arrayTpe = ir.VectorType(m.dataType, m.depth.toInt)
        state.append(ir.Reference(m.name, arrayTpe))
      case m : firrtl.CDefMemory if m.seq =>
        throw new UntimedError(s"[${mod.name}] memory ${m.name} is a SyncReadMem, for untimed modules $useMem")
      case m : firrtl.CDefMemory =>
        val arrayTpe = ir.VectorType(m.tpe, m.size.toInt)
        state.append(ir.Reference(m.name, arrayTpe))
      case other => other.foreachStmt(onStmt)
    }
    mod.foreachStmt(onStmt)

    state.toSeq
  }

  private def analyzeMethods(mod: ir.Module, calls: Iterable[MethodCallAnnotation], annos: AnnotationSeq, state: Set[String]): (Seq[MethodInfo], ir.Module) = {
    val callIO = calls.map { c => c.callIO.ref -> CallInfo(c.calleeParent.module, c.calleeName, c.callIO.ref, ir.NoInfo) }.toMap

    // method are of the following general pattern:
    // ```
    // method.guard <= UInt<1>("h1")
    // method.ret is invalid
    // when method.enabled :
    //   ; method body
    // ```
    // we know all the method names, so we can just search for a Conditionally that checks the `method_name.enabled` signal
    val ioToName = annos.collect{ case a: MethodIOAnnotation if a.target.module == mod.name => a.target.ref -> a.name }.toMap

    val methods = mutable.ArrayBuffer[MethodInfo]()

    def onStmt(s: ir.Statement): ir.Statement = s match {
      case c : ir.Conditionally => c.pred match {
        case ir.SubField(ir.Reference(ioName, _, _, _), "enabled", _, _) if ioToName.contains(ioName) =>
          assert(c.alt == ir.EmptyStmt)
          val (info, newBody) = analyzeMethod(ioToName(ioName), mod.name, ioName, c.conseq, callIO, state)
          methods.append(info)
          // the guard will be moved into the method to solely guard the state updates
          c.copy(pred = ir.UIntLiteral(1), conseq = newBody)
        case _ => c // methods should not be enclosed in other when blocks!
      }
      case c : ir.Connect => c.loc match {
        // we need to include any guards of sub methods!
        case ir.SubField(ir.Reference(ioName, _, _, _), "guard", _, _) if ioToName.contains(ioName) =>
          val method = methods.last
          assert(method.ioName == ioName, "Expected guard assignment to immediately follow method body!")
          val subGuards = method.calls.map(c => ir.SubField(ir.Reference(c.ioName), "guard"))
          val fullGuard = (subGuards :+ c.expr).reduce((a,b) => ir.DoPrim(PrimOps.And, Seq(a,b), Seq(), ir.UnknownType))
          c.copy(expr = fullGuard)
        case _ => c
      }
      // TODO: check for state updates outside of methods
      //       we can either completely disallow them or treat them as some sort of init block
      case other => other.mapStmt(onStmt)
    }
    val newMod = mod.mapStmt(onStmt).asInstanceOf[ir.Module]

    (methods.toSeq, newMod)
  }

  /**
   * We need to extract some information about the method:
   * - what state it writes to
   * - what calls it makes
   */
  private def analyzeMethod(name: String, parent: String, ioName: String, body: ir.Statement, calls: Map[String, CallInfo], state: Set[String]): (MethodInfo, ir.Statement) = {
    val locals = mutable.HashSet[String]()
    val writes = mutable.HashSet[String]()
    val localCalls = mutable.HashMap[String, ir.Info]()

    def isWrite(loc: ir.Expression): Boolean = {
      val signal = loc.serialize.split('.').head
      if(state.contains(signal)) {
        writes.add(signal)
        true
      } else { false }
    }

    val guard = ir.SubField(ir.Reference(ioName), "enabled")

    def onStmt(s: ir.Statement): ir.Statement = s match {
      case d @ ir.DefNode(_, name, _) => locals.add(name) ; d
      case d @ ir.DefWire(_, name, _) => locals.add(name) ; d
      case r : ir.DefRegister =>
        throw new UntimedError(s"Cannot create a register ${r.name} in method $name of $parent!")
      case m : ir.DefMemory =>
        throw new UntimedError(s"Cannot create a memory ${m.name} in method $name of $parent!")
      case i : ir.DefInstance =>
        throw new UntimedError(s"Cannot create an instance ${i.name} of ${i.module} in method $name of $parent!")
      case c @ ir.Connect(info, loc, expr) =>
        (loc, expr) match {
          case (ir.SubField(ir.Reference(maybeCall, _, _, _), "enabled", _, _), _) if calls.contains(maybeCall) =>
            // only use info from enabled if we haven't found better info so far
            if(!localCalls.contains(maybeCall)) { localCalls(maybeCall) = info }
            c
          case (_, ir.SubField(ir.Reference(maybeCall, _, _, _), "ret", _, _)) if calls.contains(maybeCall) =>
            // ret has better info than enabled!
            localCalls(maybeCall) = info
            c
          case _ =>
            // guard state updates
            if(isWrite(loc)) {
              ir.Conditionally(info, guard, c, ir.EmptyStmt)
            } else { c }
        }
      case c @ ir.IsInvalid(info, loc) =>
        // guard state updates
        if(isWrite(loc)) {
          ir.Conditionally(info, guard, c, ir.EmptyStmt)
        } else { c }
      case m : firrtl.CDefMPort =>
        m.direction match {
          case MInfer => throw new UntimedError(s"[name] ${m.mem}.${m.name}: inferred mem ports are not supported, use read or write directly!")
          case MReadWrite => throw new UntimedError(s"[name] ${m.mem}.${m.name}: combined read/write mem ports are not supported, use read or write!")
          case MRead => m
          case MWrite =>
            assert(state.contains(m.mem))
            writes.add(m.mem)
            // guard state update
            ir.Conditionally(m.info, guard, m, ir.EmptyStmt)
        }

      case other => other.mapStmt(onStmt)
    }
    val newBody = onStmt(body)

    // update the ir.Info for all calls:
    val callInfos = localCalls.map { case (c, i) => calls(c).copy(info=i) }

    (MethodInfo(name, parent, ioName, writes.toSet, callInfos.toSeq), newBody)
  }
}

class UntimedError(s: String) extends PassException(s)
