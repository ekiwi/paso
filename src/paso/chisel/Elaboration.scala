// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import chisel3.{MultiIOModule, RawModule}
import chisel3.hacks.{ElaborateInContextOfModule, ElaborateObserver, ExternalReference}
import firrtl.annotations.{Annotation, CircuitTarget, PresetAnnotation}
import firrtl.ir.NoInfo
import firrtl.options.Dependency
import firrtl.passes.InlineInstances
import firrtl.stage.RunFirrtlTransformAnnotation
import firrtl.{CircuitState, ir}
import logger.LogLevel
import paso.chisel.passes._
import paso.untimed.{ConnectCalls, ResetToZeroPass}
import paso.verification.{Assertion, BasicAssertion, MethodSemantics, ProtocolInterpreter, Spec, StepNode, Subspec, UntimedModel, VerificationProblem}
import paso.{IsSubmodule, ProofCollateral, Protocol, ProtocolSpec, SubSpecs, UntimedModule}
import uclid.smt

case class Elaboration() {
  private var chiselElaborationTime = 0L
  private var firrtlCompilerTime = 0L
  private def elaborate[M <: RawModule](gen: () => M): (firrtl.CircuitState, M) = {
    val start = System.nanoTime()
    val res = ChiselCompiler.elaborate(gen)
    chiselElaborationTime += System.nanoTime() - start
    res
  }
  private def lowerTypes(tup: (ir.Circuit, Seq[Annotation])): (ir.Circuit, Seq[Annotation]) = {
    val st = CircuitState(tup._1, tup._2)
    // TODO: we would like to lower bundles but not vecs ....
    val start = System.nanoTime()
    val st_no_bundles = firrtl.passes.LowerTypes.runTransform(st)
    firrtlCompilerTime += System.nanoTime() - start
    (st_no_bundles.circuit, st_no_bundles.annotations)
  }
  private def toLowFirrtl(c: ir.Circuit, annos: Seq[Annotation] = Seq()): (ir.Circuit, Seq[Annotation]) = {
    val start = System.nanoTime()
    val st = FirrtlCompiler.toLowFirrtl(CircuitState(c, annos))
    firrtlCompilerTime += System.nanoTime() - start
    (st.circuit, st.annotations)
  }
  private def toHighFirrtl(c: ir.Circuit, annos: Seq[Annotation] = Seq()): (ir.Circuit, Seq[Annotation]) = {
    val start = System.nanoTime()
    val st = FirrtlCompiler.toHighFirrtl(CircuitState(c, annos))
    firrtlCompilerTime += System.nanoTime() - start
    (st.circuit, st.annotations)
  }
  private def getMain(c: ir.Circuit): ir.Module = c.modules.find(_.name == c.main).get.asInstanceOf[ir.Module]
  private def getNonMain(c: ir.Circuit): Seq[ir.Module] = c.modules.filter(_.name != c.main)map(_.asInstanceOf[ir.Module])

  private def elaborateInContext(ctx: RawModule, gen: () => Unit): firrtl.CircuitState = {
    val start = System.nanoTime()
    val r = ElaborateInContextOfModule(ctx, gen)
    chiselElaborationTime += System.nanoTime() - start
    r
  }

  private def elaborateObserver(observing: Iterable[RawModule], name: String, gen: () => Unit): (firrtl.CircuitState, Seq[ExternalReference]) = {
    val start = System.nanoTime()
    val r = ElaborateObserver(observing, name, gen)
    chiselElaborationTime += System.nanoTime() - start
    r
  }


  private def compileInvariant(state: CircuitState, refs: Seq[ExternalReference], exposedSignals: Map[String, (String, ir.Type)]): Seq[Assertion] = {
    // convert refs to exposed signals
    val annos = refs.map{ r =>
      val (_, tpe) = exposedSignals(s"${r.signal.circuit}.${r.nameInObserver}")
      CrossModuleInput(r.nameInObserver, r.signal.circuit, tpe)
    } ++ Seq(RunFirrtlTransformAnnotation(Dependency(passes.CrossModuleReferencesToInputsPass)),
    RunFirrtlTransformAnnotation(Dependency[passes.AssertsToOutputs]))

    // convert invariant module to SMT
    val (transitionSystem, resAnnos) = FirrtlToFormal(state.circuit, state.annotations ++ annos, LogLevel.Error)

    // extract the assertions from the transition system outputs
    val asserts = resAnnos.collect{ case a : AssertEnable =>
      val en = transitionSystem.outputs.find(_._1 == a.name + "_en").map(_._2).get
      val pred = transitionSystem.outputs.find(_._1 == a.name + "_pred").map(_._2).get
      BasicAssertion(en, pred)
    }
    //val a  = new FirrtlInvarianceInterpreter(lo.circuit, lo.annotations).run().asserts

    // rename cross module references
    // e.g. RandomLatency_running -> RandomLatency.signals_running
    val prefixRenames = refs.map{ r =>
      val (portName, _) = exposedSignals(s"${r.signal.circuit}.${r.nameInObserver}")
      r.signal.circuit -> s"${r.signal.circuit}.$portName"
    }.toSet.toList
    // TODO: propagate prefix renames to namespacing....

    asserts
  }

  private def elaborateProtocols(protos: Seq[paso.Protocol], methods: Map[String, MethodSemantics]): Seq[(String, StepNode)] = {
    protos.map{ p =>
      //println(s"Protocol for: ${p.methodName}")
      val (state, _) = elaborate(() => new MultiIOModule() { p.generate(clock) })
      val (ff, annos) = lowerTypes(toHighFirrtl(state.circuit, state.annotations))
      val int = new ProtocolInterpreter(enforceNoInputAfterOutput = false)
      //println(ff.serialize)
      new FirrtlProtocolInterpreter(p.methodName, ff, annos, int, p.stickyInputs).run()
      (p.methodName, int.getGraph(p.methodName))
    }
  }

  private def elaborateImpl(impl: ChiselImpl[_], subspecs: Seq[IsSubmodule], externalRefs: Iterable[ExternalReference]): FormalSys = {
    // We mark the ones that we want to expose as outputs as DoNotInline and then run the PasoFlatten pass to do the rest.
    val doNotInlineAnnos = subspecs.map(s => DoNotInlineAnnotation(s.module))
    val state = CircuitState(impl.circuit, impl.annos ++ doNotInlineAnnos)
    compileToFormal(state, externalRefs)
  }

  /** used for both: RTL implementation and untimed module spec */
  private case class FormalSys(model: smt.TransitionSystem, submodules: Map[String, String], exposedSignals: Map[String, (String, ir.Type)])
  private def compileToFormal(state: CircuitState, externalRefs: Iterable[ExternalReference], ll: LogLevel.Value = LogLevel.Error): FormalSys = {
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

    // update external references with the type derived from the exposed signal
    val exposed = resAnnos.collect { case ExposedSignalAnnotation(name, portName, tpe) =>
      s"$circuitName.$name" -> (portName, tpe)
    }.toMap

    FormalSys(transitionSystem, submoduleNames, exposed)
  }

  private case class Untimed[S <: UntimedModule](state: Seq[State], model: UntimedModel, protocols: Seq[Protocol])
  private def elaborateUntimed[S <: UntimedModule](spec: ChiselSpec[S], externalRefs: Iterable[ExternalReference]): Untimed[S] = {
    // connect all calls inside the module (TODO: support for bindings with UFs)
    val fixedCalls = ConnectCalls.run(spec.untimed.getChirrtl, Set())
    // make sure that all state is initialized to its reset value or zero
    val reset = CircuitTarget(fixedCalls.circuit.main).module(fixedCalls.circuit.main).ref("reset")
    val initAnnos = Seq(RunFirrtlTransformAnnotation(Dependency(ResetToZeroPass)), PresetAnnotation(reset))
    // convert to formal
    val withAnnos = fixedCalls.copy(annotations = fixedCalls.annotations ++ initAnnos)
    val formal = compileToFormal(withAnnos, externalRefs, ll = LogLevel.Error)

    // now we need to convert the transition system into the (more or less "legacy") UntimedModel format

    val state = formal.model.states // TODO: make sure all states have proper init value (in ConnectCalls)
    //val methods =

    // TODO
    val model = UntimedModel(spec.untimed.name, Seq(), Map(), Map())
    println("TODO: translate untimed module into SMT")

    // FIXME: remember that by default every state is initialized to zero if not other init value is specified

    Untimed(Seq(), model, spec.protos)
  }

  private def elaborateSpec[S <: UntimedModule](spec: ChiselSpec[S], externalRefs: Iterable[ExternalReference]) = {
    val ut = elaborateUntimed(spec, externalRefs)
    val pt = elaborateProtocols(ut.protocols, ut.model.methods)
    (Spec(ut.model, pt.toMap), ut.state)
  }

  case class ChiselImpl[M <: RawModule](instance: M, circuit: ir.Circuit, annos: Seq[Annotation])
  private def chiselElaborationImpl[M <: RawModule](gen: () => M): ChiselImpl[M] = {
    val (state, ip) = elaborate(gen)
    ChiselImpl(ip, state.circuit, state.annotations)
  }
  case class ChiselSpec[S <: UntimedModule](untimed: S, protos: Seq[Protocol])
  private def chiselElaborationSpec[S <: UntimedModule](gen: () => ProtocolSpec[S]): ChiselSpec[S] = {
    var ip: Option[ProtocolSpec[S]] = None
    val elaborated = UntimedModule.elaborate { ip = Some(gen()) ; ip.get.spec }
    ChiselSpec(elaborated, ip.get.protos)
  }

  def apply[I <: RawModule, S <: UntimedModule](impl: () => I, proto: (I) => ProtocolSpec[S], findSubspecs: (I,S) => SubSpecs[I,S], inv: (I, S) => ProofCollateral[I, S]): VerificationProblem = {
    firrtlCompilerTime = 0L
    chiselElaborationTime = 0L
    val start = System.nanoTime()

    // Chisel elaboration for implementation and spec
    val implChisel = chiselElaborationImpl(impl)
    val specChisel = chiselElaborationSpec(() => proto(implChisel.instance))
    val subspecList = findSubspecs(implChisel.instance, specChisel.untimed).subspecs
    assert(implChisel.instance.name != specChisel.untimed.name, "spec and impl must have different names")

    // elaborate invariants in order to collect all signals that need to be exposed from the implementation and spec
    val collateral = inv(implChisel.instance, specChisel.untimed)
    val elaboratedMaps = collateral.maps.map{ m =>
      elaborateObserver(List(implChisel.instance, specChisel.untimed), "map", {() => m(implChisel.instance, specChisel.untimed)})
    }
    val elaboratedInvs = collateral.invs.map{ i =>
      elaborateObserver(List(implChisel.instance), "inv", () => i(implChisel.instance))
    }
    val externalReferences = elaboratedMaps.flatMap(_._2) ++ elaboratedInvs.flatMap(_._2)

    // Firrtl Compilation
    val implementation = elaborateImpl(implChisel, subspecList, externalReferences)
    val endImplementation = System.nanoTime()
    val (spec, untimed_state) = elaborateSpec(specChisel, externalReferences)
    val endSpec= System.nanoTime()

    // elaborate subspecs
    val implIo = implementation.model.inputs ++ implementation.model.outputs.map(o => smt.Symbol(o._1, o._2.typ))
    val subspecs = subspecList.map { s =>
      val elaborated = chiselElaborationSpec(s.makeSpec)
      val (spec, _) = elaborateSpec[UntimedModule](elaborated, List())
      val instance = implementation.submodules(s.module.name)
      val prefixLength = instance.length + 1
      val io = implIo.filter(_.id.startsWith(instance + ".")).map(s => s.copy(id = s.id.substring(prefixLength)))
      val binding = s.getBinding.map(_.instance)
      Subspec(instance, io, spec, binding)
    }
    val endSubSpec= System.nanoTime()

    // elaborate the proof collateral
    val exposedSignals = implementation.exposedSignals
    val mappings = elaboratedMaps.flatMap(m => compileInvariant(m._1, m._2, exposedSignals))
    val invariants = elaboratedInvs.flatMap(m => compileInvariant(m._1, m._2, exposedSignals))
    val endBinding = System.nanoTime()

    if(true) {
      val total = endBinding - start
      val dImpl = endImplementation - start
      val dSpec = endSpec - endImplementation
      val dSubspec = endSubSpec - endSpec
      val dBinding = endBinding - endSubSpec
      def p(i: Long): Long = i * 100 / total
      def ms(i: Long): Long = i / 1000 / 1000
      println(s"Total Elaboration Time: ${ms(total)}ms")
      println(s"${p(dImpl)}% RTL, ${p(dSpec)}% Spec (Untimed + Protocol), ${p(dSubspec)}% Subspecs, ${p(dBinding)}% Invariances + Mapping")
      val other = total - firrtlCompilerTime - chiselElaborationTime
      println(s"${p(chiselElaborationTime)}% Chisel Elaboration, ${p(firrtlCompilerTime)}% Firrtl Compiler, ${p(other)}% Rest")
      println(s"TODO: correctly account for the time spent in FirrtlToFormal running the firrtl compiler and yosys and btor parser")
    }


    // combine into verification problem
    val prob = VerificationProblem(
      impl = implementation.model,
      spec = spec,
      subspecs = subspecs,
      invariances = invariants,
      mapping = mappings
    )

    prob
  }
}
