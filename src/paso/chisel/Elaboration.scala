// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import chisel3.{MultiIOModule, RawModule}
import chisel3.hacks.{ElaborateObserver, ExternalReference}
import firrtl.annotations.{Annotation, CircuitTarget}
import firrtl.options.Dependency
import firrtl.passes.InlineInstances
import firrtl.stage.RunFirrtlTransformAnnotation
import firrtl.{AnnotationSeq, CircuitState, ir}
import logger.LogLevel
import maltese.mc.{IsOutput, TransitionSystem}
import maltese.passes.{AddForallQuantifiers, DeadCodeElimination, Inline, PassManager, QuantifiedVariable, Simplify}
import paso.chisel.passes._
import paso.{ForallAnnotation, IsSubmodule, ProofCollateral, ProtocolSpec, SubSpecs, UntimedModule, untimed}
import paso.verification.{Spec, UntimedModel, VerificationProblem}
import maltese.{mc, smt}
import maltese.smt.solvers.Yices2SMTLib
import paso.protocols.{Protocol, ProtocolCompiler, ProtocolGraph, SymbolicProtocolInterpreter}
import paso.untimed.AbstractModuleAnnotation

case class Elaboration() {
  private def elaborate[M <: RawModule](gen: () => M): (firrtl.CircuitState, M) = {
    val res = ChiselCompiler.elaborate(gen)
    res
  }

  private def elaborateObserver(observing: Iterable[RawModule], name: String, gen: () => Unit): (firrtl.CircuitState, Seq[ExternalReference]) = {
    val r = ElaborateObserver(observing, name, gen)
    r
  }

  private def compileInvariant(inv: ChiselInvariants, exposedSignals: Seq[ExposedSignalAnnotation]): mc.TransitionSystem = {
    // There could be multiple annotations for a single exposed signals that was lowered to ground types.
    // We use the original nameInObserver to filter out any such duplicates.
    val exposed = exposedSignals.groupBy(_.nameInObserver).map(_._2.head)
    val invModuleRef = CircuitTarget(inv.state.circuit.main).module(inv.state.circuit.main)
    val annos = exposed.map{ r =>
      if(r.isMemory) CrossModuleMem(invModuleRef.ref(r.nameInObserver), r.depth, r.tpe)
      else CrossModuleInput(invModuleRef.ref(r.nameInObserver), r.tpe)
    } ++ Seq(RunFirrtlTransformAnnotation(Dependency(passes.CrossModuleReferencesToInputsPass))) ++
    // add an invertAsserts port that turns asserts into assumes when active
    Seq(RunFirrtlTransformAnnotation(Dependency(passes.InvertAssertPass)))

    // convert invariant module to SMT
    val (transitionSystem, resAnnos) = FirrtlToFormal(inv.state.circuit, inv.state.annotations ++ annos, LogLevel.Error)
    val sys = mc.TransitionSystem.prefixSignals(transitionSystem)

    // connect cross module reference inputs
    val inputConnections = exposedSignals.filterNot(_.isMemory).map { signal =>
      // the name of the signal coming out of the observed circuit
      val outputName = s"${signal.target.module}.${signal.target.ref}"
      // the prefix of the matching input we expect
      val signalName = s"${sys.name}.${signal.nameInObserver}"
      // find input symbol
      val sym = sys.inputs.find(_.name == signalName)
        .getOrElse(throw new RuntimeException(s"TODO: support non-ground type signals to be observed: $signalName"))
      sym.name -> sym.rename(outputName)
    }
    val connectedInputs = mc.TransitionSystem.connect(sys, inputConnections.toMap)

    // connect mems if there are any
    val memReplacements =  exposedSignals.filter(_.isMemory).map { signal =>
      // the name of the signal coming out of the observed circuit
      val outputName = s"${signal.target.module}.${signal.target.ref}"
      // the prefix of the matching input we expect
      val signalName = s"${sys.name}.${signal.nameInObserver}"
      // find state symbol
      val sym = sys.states.map(_.sym).find(_.name == signalName)
        .getOrElse(throw new RuntimeException(s"TODO: support non-ground type signals to be observed: $signalName"))
      sym.name -> sym.rename(outputName)
    }
    val connectedState = mc.TransitionSystem.connectStates(connectedInputs, memReplacements.toMap)

    // add quantifiers
    val quantifiedVariables = resAnnos.collect{ case ForallAnnotation(target, width, start, end) =>
      QuantifiedVariable(smt.BVSymbol(target.module + "." + target.ref, width), start, end)
    }
    val withQuantifiers = AddForallQuantifiers.run(connectedState, quantifiedVariables)

    //println(connectedState.serialize)
    //println()
    //println(withQuantifiers.serialize)

    withQuantifiers
  }

  private def compileProtocol(proto: Protocol, implName: String, specName: String): ProtocolGraph = {
    //println(s"Protocol for: ${p.methodName}")
    val (state, _) = elaborate(() => new MultiIOModule() {
      override def circuitName: String = proto.methodName + "Protocol"
      override def desiredName: String = circuitName
      proto.generate(clock)
    })
    val normalized = ProtocolCompiler.run(state, ioPrefix = f"$implName.io", specName = specName, methodName = proto.methodName)
    val solver = new Yices2SMTLib()
    val paths = new SymbolicProtocolInterpreter(normalized, proto.stickyInputs, solver).run()
    ProtocolGraph.encode(paths)
  }

  private def compileImpl(impl: ChiselImpl[_], subspecs: Seq[IsSubmodule], externalRefs: Iterable[ExternalReference]): FormalSys = {
    // We mark the ones that we want to expose as outputs as DoNotInline and then run the PasoFlatten pass to do the rest.
    val doNotInlineAnnos = subspecs.map(s => DoNotInlineAnnotation(s.module))
    val state = CircuitState(impl.circuit, impl.annos ++ doNotInlineAnnos)
    compileToFormal(state, externalRefs, prefix = "")
  }

  /** used for both: RTL implementation and untimed module spec */
  private case class FormalSys(model: TransitionSystem, submodules: Map[String, String], exposedSignals: Seq[ExposedSignalAnnotation], annos: AnnotationSeq)
  private def compileToFormal(state: CircuitState, externalRefs: Iterable[ExternalReference], prefix: String, ll: LogLevel.Value = LogLevel.Error): FormalSys = {
    // We want to wire all external signals to the toplevel
    val circuitName = state.circuit.main
    val exposeSignalsAnnos = externalRefs.filter(_.signal.circuit == circuitName)
      .map(r => SignalToExposeAnnotation(r.signal, r.nameInObserver)) ++ Seq(
      RunFirrtlTransformAnnotation(Dependency(passes.ExposeSignalsPass)),
      RunFirrtlTransformAnnotation(Dependency[firrtl.passes.wiring.WiringTransform])
    )

    // The firrtl SMT backend expects all submodules that are part of the implementation to be inlined.
    // Any DoNotInline annotation from the `state.annotations` will prevent that particular module to be inlined.
    val doFlatten = Seq(RunFirrtlTransformAnnotation(Dependency(passes.PasoSubmoduleFlatten)),
      RunFirrtlTransformAnnotation(Dependency[InlineInstances]))
    val annos = state.annotations ++ exposeSignalsAnnos ++ doFlatten
    val (transitionSystem, resAnnos) = FirrtlToFormal(state.circuit, annos, ll)
    val submoduleNames = resAnnos.collect{ case a : SubmoduleInstanceAnnotation =>
      a.originalModule -> a.target.instance
    }.toMap

    // collect information about exposed signals
    val exposed = resAnnos.collect { case a : ExposedSignalAnnotation => a }

    // add prefix to transition system before namespacing
    val withPrefix = transitionSystem.copy(name = prefix + transitionSystem.name)

    // namespace the transition system
    val namespaced = mc.TransitionSystem.prefixSignals(withPrefix)

    FormalSys(namespaced, submoduleNames, exposed, resAnnos)
  }

  private case class Untimed(model: UntimedModel, protocols: Seq[Protocol], exposedSignals: Seq[ExposedSignalAnnotation])
  private def compileUntimed(spec: ChiselSpec[UntimedModule], externalRefs: Iterable[ExternalReference], prefix: String = "", abstracted: Iterable[AbstractModuleAnnotation] = List()): Untimed = {
    // abstract any methods
    val abstractedMethods = untimed.UninterpretedMethods.run(spec.untimed.getChirrtl, abstracted)
    // connect all calls inside the module
    val fixedCalls = untimed.ConnectCalls.run(abstractedMethods)

    // ext modules are used to model UFs and thus should not be inlined
    val circuit = CircuitTarget(fixedCalls.circuit.main)
    val noInlineAnnos = fixedCalls.circuit.modules.collect{ case m: ir.ExtModule => DoNotInlineAnnotation(circuit.module(m.name)) }
    // make sure that all state is initialized to its reset value or zero
    val initAnnos = Seq(RunFirrtlTransformAnnotation(Dependency(untimed.ResetToZeroPass)))
    // convert to formal
    val withAnnos = fixedCalls.copy(annotations = fixedCalls.annotations ++ initAnnos ++ noInlineAnnos)
    val formal = compileToFormal(withAnnos, externalRefs, prefix=prefix, ll = LogLevel.Error)
    val sys = formal.model

    // Extract information about all methods
    val info = fixedCalls.annotations.collectFirst{ case untimed.UntimedModuleInfoAnnotation(_, i) => i }.get
    assert(sys.name == prefix + info.name)
    val methods = info.methods.map { m =>
      val mWithPrefix = m.copy(parent = sys.name)
      val fullIoName = mWithPrefix.fullIoName
      val args = sys.inputs.filter(_.name.startsWith(fullIoName + "_arg")).map(s => s.name -> s.width)
      val ret = sys.signals.filter(s => s.lbl == IsOutput && s.name.startsWith(fullIoName + "_ret"))
        .map(s => s.name -> s.e.asInstanceOf[smt.BVExpr].width)
      mWithPrefix.copy(args=args, ret=ret)
    }

    // Memories in Firrtl cannot have a synchronous reset, we thus need to convert the reset after the fact
    val reset = smt.BVSymbol(sys.name + "." + "reset", 1)
    val states = sys.states.map {
      case s @ mc.State(sym: smt.BVSymbol, init, Some(next)) =>
        assert(init.isEmpty)
        s
      case mc.State(sym: smt.ArraySymbol, Some(init: smt.ArrayExpr), Some(next: smt.ArrayExpr)) =>
        mc.State(sym, None, Some(smt.ArrayIte(reset, init, next)))
      case other => throw new RuntimeException(s"Unexpected state: $other")
    }
    val sysWithSynchronousMemInit = sys.copy(states = states)

    // Simplify Transition System
    val simplifiedSys = simplifyTransitionSystem(sysWithSynchronousMemInit)
    val model = UntimedModel(simplifiedSys, methods)

    Untimed(model, spec.protos, formal.exposedSignals)
  }

  private val simplificationPasses = PassManager(List(
    Simplify, new Inline(), DeadCodeElimination,
    Simplify, new Inline(), DeadCodeElimination,
    Simplify
  ))

  private def simplifyTransitionSystem(sys: TransitionSystem): TransitionSystem =
    simplificationPasses.run(sys, trace = false)

  private def compileSpec(spec: ChiselSpec[UntimedModule], implName: String, externalRefs: Iterable[ExternalReference],
    prefix: String = "", abstracted: Iterable[AbstractModuleAnnotation] = List()):
  (Spec, Seq[ExposedSignalAnnotation]) = {
    val ut = compileUntimed(spec, externalRefs, prefix = prefix, abstracted = abstracted)
    val pt = ut.protocols.map(compileProtocol(_, implName, ut.model.name))
    (Spec(ut.model, pt), ut.exposedSignals)
  }

  case class ChiselImpl[M <: RawModule](instance: M, circuit: ir.Circuit, annos: Seq[Annotation])
  private def chiselElaborationImpl[M <: RawModule](gen: () => M): ChiselImpl[M] = {
    val (state, ip) = elaborate(gen)
    ChiselImpl(ip, state.circuit, state.annotations)
  }
  case class ChiselSpec[+S <: UntimedModule](untimed: S, protos: Seq[Protocol])
  private def chiselElaborationSpec[S <: UntimedModule](gen: () => ProtocolSpec[S]): ChiselSpec[S] = {
    var ip: Option[ProtocolSpec[S]] = None
    val elaborated = UntimedModule.elaborate { ip = Some(gen()) ; ip.get.spec }
    ChiselSpec(elaborated, ip.get.protos)
  }

  case class ChiselInvariants(state: firrtl.CircuitState, externalRefs: Seq[ExternalReference])
  private def chiselElaborateInvariants[M <: RawModule, S <: UntimedModule]
  (impl: ChiselImpl[M], spec: ChiselSpec[S], proofCollateral: (M, S) => ProofCollateral[M, S]): ChiselInvariants = {
    val collateral = proofCollateral(impl.instance, spec.untimed)
    val genAll = () => {
      val enabled = chisel3.experimental.IO(chisel3.Input(chisel3.Bool())).suggestName("enabled")
      chisel3.when(enabled) {
        collateral.invs.foreach(i => i(impl.instance))
        collateral.maps.foreach(m => m(impl.instance, spec.untimed))
      }
      ()
    }
    val (state, externalRefs) = elaborateObserver(List(impl.instance, spec.untimed), "Invariants", genAll)
    ChiselInvariants(state, externalRefs)
  }

  def apply[I <: RawModule, S <: UntimedModule](impl: () => I, proto: (I) => ProtocolSpec[S], findSubspecs: (I,S) => SubSpecs[I,S], proofCollateral: (I, S) => ProofCollateral[I, S]): VerificationProblem = {
    // Chisel elaboration for implementation and spec
    val implChisel = chiselElaborationImpl(impl)
    val specChisel = chiselElaborationSpec(() => proto(implChisel.instance))
    val subspecList = findSubspecs(implChisel.instance, specChisel.untimed).subspecs
    assert(implChisel.instance.name != specChisel.untimed.name, "spec and impl must have different names")

    // TODO: we might have to evaluate subspecs here in order to make them available to the invariants

    // elaborate invariants in order to collect all signals that need to be exposed from the implementation and spec
    val invChisel = chiselElaborateInvariants(implChisel, specChisel, proofCollateral)

    // Firrtl Compilation
    val implementation = compileImpl(implChisel, subspecList, invChisel.externalRefs)
    // find submodules the methods of which will be replaced with uninterpreted functions
    val abstractModules = subspecList.flatMap(_.getBinding).map{ target =>
      val prefix = (target.module +: target.asPath.map(_._1.value)).mkString(".")
      AbstractModuleAnnotation(target, prefix)
    }
    val (spec, specExposedSignals) = compileSpec(specChisel, implementation.model.name, invChisel.externalRefs, abstracted=abstractModules)

    // elaborate + compile subspecs
    val subspecs = subspecList.map { s =>
      val elaborated = chiselElaborationSpec(s.makeSpec)
      val instance = implementation.submodules(s.module.name)
      val prefix = implementation.model.name + "." + instance
      // if teh submodule is bound, we need to replace method implementations with uninterpreted functions
      val abstractModules = s.getBinding.map { bound =>
        val prefix = (bound.module +: bound.asPath.map(_._1.value)).mkString(".")
        val target = CircuitTarget(elaborated.untimed.name).module(elaborated.untimed.name)
        AbstractModuleAnnotation(target, prefix)
      }
      compileSpec(elaborated, prefix, List(), prefix = prefix + ".", abstracted = abstractModules)._1
    }

    // elaborate the proof collateral
    val exposed = implementation.exposedSignals ++ specExposedSignals
    val inv = compileInvariant(invChisel, exposed)

    // combine into verification problem
    val prob = VerificationProblem(implementation.model, spec, subspecs, inv)

    prob
  }
}
