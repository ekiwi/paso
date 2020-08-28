// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import chisel3.{MultiIOModule, RawModule}
import chisel3.hacks.elaborateInContextOfModule
import firrtl.annotations.Annotation
import firrtl.ir.{BundleType, NoInfo}
import firrtl.options.Dependency
import firrtl.passes.InlineInstances
import firrtl.stage.RunFirrtlTransformAnnotation
import firrtl.{CircuitState, ir}
import paso.chisel.passes.{ChangeAnnotationCircuit, DoNotInlineAnnotation, FindModuleState, FixClockRef, FixReset, RemoveInstances, ReplaceMemReadWithVectorAccess, State, SubmoduleIOAnnotation}
import paso.verification.{Assertion, MethodSemantics, ProtocolInterpreter, Spec, StepNode, Subspec, UntimedModel, VerificationProblem}
import paso.{IsSubmodule, ProofCollateral, Protocol, ProtocolSpec, SubSpecs, SubmoduleAnnotation, UntimedModule}
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

  private def elaborate(ctx0: RawModule, ctx1: RawModule, name: String, gen: () => Unit): (firrtl.ir.Circuit, Seq[Annotation]) = {
    val start = System.nanoTime()
    val r = elaborateInContextOfModule(ctx0, ctx1, name, gen)
    chiselElaborationTime += System.nanoTime() - start
    r
  }
  private def elaborate(ctx0: RawModule, gen: () => Unit, submoduleRefs: Boolean = false): (firrtl.ir.Circuit, Seq[Annotation]) = {
    val start = System.nanoTime()
    val r = elaborateInContextOfModule(ctx0, gen, submoduleRefs)
    chiselElaborationTime += System.nanoTime() - start
    r
  }

  // TODO: add support for implementations and untimed models that contain actual Vecs
  //       currently we use the VectorType as a placeholder for memories....
  private def stateToPort(state: Iterable[State], prefix: String): Iterable[ir.Port] =
    state.collect { case State(name, tpe, _) => ir.Port(NoInfo, prefix + name, ir.Input, tpe) }
  private def collectMemTypes(state: Iterable[State], prefix: String): Iterable[(String, ir.VectorType)] =
    state.collect{ case State(name, tpe: ir.VectorType, _) => prefix + name -> tpe }

  private def elaborateMappings[IM <: RawModule, SM <: UntimedModule](
      impl: IM, impl_state: Seq[State],
      spec: SM, spec_state: Seq[State], maps: Seq[(IM, SM) => Unit]): Seq[Assertion] = {
    val map_ports = stateToPort(impl_state, impl.name + ".") ++ stateToPort(spec_state, spec.name + ".") ++
      Seq(ir.Port(NoInfo, "clock", ir.Input, ir.ClockType))
    val map_mod = ir.Module(NoInfo, name = "m", ports=map_ports.toSeq, body=ir.EmptyStmt)
    val memTypes = (collectMemTypes(impl_state, impl.name + ".") ++ collectMemTypes(spec_state, spec.name + ".")).toMap

    maps.flatMap { m =>
      val mod = elaborate(impl, spec, "map", {() => m(impl, spec)})
      val body = mod._1.modules.head.asInstanceOf[ir.Module].body
      val c = ir.Circuit(NoInfo, Seq(map_mod.copy(body=body)), map_mod.name)

      // HACK: replace all read ports (and inferred ports b/c yolo) with vector accesses
      val c_fixed = ReplaceMemReadWithVectorAccess(memTypes)(c)

      val elaborated = toHighFirrtl(c_fixed, mod._2)
      new FirrtlInvarianceInterpreter(elaborated._1, elaborated._2).run().asserts
    }
  }

  private def elaborateInvariances[IM <: RawModule](impl: IM, impl_state: Seq[State], invs: Seq[IM => Unit]): Seq[Assertion] = {
    val inv_ports = stateToPort(impl_state, "") ++ Seq(ir.Port(NoInfo, "clock", ir.Input, ir.ClockType))
    val inv_mod = ir.Module(NoInfo, name = "i", ports=inv_ports.toSeq, body=ir.EmptyStmt)
    val memTypes = collectMemTypes(impl_state, "").toMap

    invs.flatMap { ii =>
      val mod = elaborate(impl, {() => ii(impl)}, submoduleRefs = true)
      val body = mod._1.modules.head.asInstanceOf[ir.Module].body
      val c = ir.Circuit(NoInfo, Seq(inv_mod.copy(body=body)), inv_mod.name)
      // HACK: replace all read ports (and inferred ports b/c yolo) with vector accesses
      val c_fixed = ReplaceMemReadWithVectorAccess(memTypes)(c)
      val elaborated = lowerTypes(toHighFirrtl(c_fixed, mod._2))
      new FirrtlInvarianceInterpreter(elaborated._1, elaborated._2).run().asserts
    }
  }

  private def elaborateProtocols(protos: Seq[paso.Protocol], methods: Map[String, MethodSemantics]): Seq[(String, StepNode)] = {
    protos.map{ p =>
      //println(s"Protocol for: ${p.methodName}")
      val (state, _) = elaborate(() => new MultiIOModule() { p.generate(p.methodName + "_", clock) })
      val (ff, annos) = lowerTypes(toHighFirrtl(state.circuit, state.annotations))
      val int = new ProtocolInterpreter(enforceNoInputAfterOutput = false)
      //println(ff.serialize)
      new FirrtlProtocolInterpreter(p.methodName, ff, annos, int, p.stickyInputs).run()
      (p.methodName, int.getGraph(p.methodName))
    }
  }

  private case class Impl[IM <: RawModule](state: Seq[State], model: smt.TransitionSystem, submoduleIO: Seq[String])
  private def elaborateImpl[IM <: RawModule](impl: ChiselImpl[IM], subspecs: Seq[IsSubmodule]): Impl[IM] = {
    // The firrtl SMT backend expects all submodules that are part of the implementation to be inlined.
    // We mark the ones that we want to expose as outputs as DoNotInline and then run the PasoFlatten pass to do the
    // rest.
    val doFlatten = Seq(RunFirrtlTransformAnnotation(Dependency(passes.PasoFlatten)),
      RunFirrtlTransformAnnotation(Dependency[InlineInstances]))
    val doNotInlineAnnos = subspecs.map(s => DoNotInlineAnnotation(s.instance))
    val (transitionSystem, resAnnos) = FirrtlToFormal(impl.circuit, impl.annos ++ doFlatten ++ doNotInlineAnnos)
    val submoduleIO = resAnnos.collect{ case a : SubmoduleIOAnnotation => a.target }
    val submoduleIONames = submoduleIO.map { t =>
      assert(t.path.length == 1, "All remaining submodules should be exactly one instance deep")
      t.path.head._1.value + "." + t.ref
    }
    Impl(List(), transitionSystem, submoduleIONames)
  }

  private case class Untimed[S <: UntimedModule](state: Seq[State], model: UntimedModel, protocols: Seq[Protocol])
  private def elaborateUntimed[S <: UntimedModule](spec: ChiselSpec[S]): Untimed[S] = {
    val spec_name = spec.circuit.main
    val modules = spec.circuit.modules.map(_.asInstanceOf[ir.Module])
    val (spec_state, untimed_model) = elaborateUntimed(spec_name, spec.untimed, modules, spec.annos)
    Untimed(spec_state, untimed_model, spec.protos)
  }


  private def elaborateUntimed(spec_name: String, untimed: UntimedModule, modules: Seq[ir.Module], annos: Seq[Annotation]): (Seq[State], UntimedModel) = {
    val main = modules.find(_.name == spec_name).get
    val spec_state = FindModuleState().run(main)
    val (spec_module, spec_subinstances) = RemoveInstances().run(main)

    // elaborate submodules first
    val subModules = spec_subinstances.map { case (instanceName, moduleName) =>
      val instance = annos.collect{ case SubmoduleAnnotation(_, in) => in }.find(_.instanceName == instanceName).get
      val (subState, subUntimed) =  elaborateUntimed(moduleName, instance, modules, annos)
      assert(subState.isEmpty, s"Submodules with state are not supported at the moment! ${instanceName}, $subState")
      instanceName -> subUntimed
    }

    val methods = untimed.methods.map { meth =>
      val (raw_firrtl, raw_annos) = elaborate(untimed, meth.generate)

      // build module for this method:
      val method_body = getMain(raw_firrtl).body
      val comb_body = ir.Block(Seq(spec_module.body, method_body))
      val comb_ports = spec_module.ports ++ getMain(raw_firrtl).ports
      val comb_mod = spec_module.copy(ports=comb_ports, body=comb_body)
      val comb_c = ir.Circuit(NoInfo, Seq(FixReset(comb_mod)), spec_name)

      // HACK: patch the incorrect references to clock that come from gen() using `this` to refer to the module
      val comb_c_fixed = FixClockRef(ir.Reference("clock", ir.ClockType))(comb_c)

      // fix annotations by changing the circuit name
      val fixAnno = ChangeAnnotationCircuit(comb_c.main)
      val fixed_annos = raw_annos.map(fixAnno(_))

      // compile combined module down to low firrtl
      val (ff, annos) = toLowFirrtl(comb_c_fixed, fixed_annos)

      // println(ff.serialize)

      val semantics = new FirrtlUntimedMethodInterpreter(ff, annos).run().getSemantics
      //val semantics = MethodSemantics(smt.BooleanLit(true), Seq(), Seq(), Seq())
      meth.name -> semantics
    }.toMap

    def toSymbol(name: String, tpe: ir.Type): smt.Symbol = smt.Symbol(name, firrtlToSmtType(tpe))
    def defaultInitVec(tpe: ir.VectorType): smt.Expr = tpe.tpe match {
      case t : ir.GroundType => smt.ConstArray(defaultInitGround(t), firrtlToSmtType(tpe).asInstanceOf[smt.ArrayType])
    }
    def defaultInitGround(tpe: ir.GroundType): smt.Expr = tpe match {
      case ir.UIntType(ir.IntWidth(w)) => if(w > 1) smt.BitVectorLit(0, w.toInt) else smt.BooleanLit(false)
      case ir.SIntType(ir.IntWidth(w)) => if(w > 1) smt.BitVectorLit(0, w.toInt) else smt.BooleanLit(false)
    }
    val spec_smt_state = spec_state.map {
      case State(name, tpe, Some(init)) => smt.State(toSymbol(name, tpe), Some(init))
      case State(name, tpe : ir.VectorType, None) => smt.State(toSymbol(name, tpe), Some(defaultInitVec(tpe)))
      case State(name, tpe : ir.GroundType, None) => smt.State(toSymbol(name, tpe), Some(defaultInitGround(tpe)))
    }
    val ut = UntimedModel(name = spec_name, state = spec_smt_state, methods = methods, sub = subModules)
    (spec_state, ut)
  }

  private def elaborateSpec[S <: UntimedModule](spec: ChiselSpec[S]) = {
    val ut = elaborateUntimed(spec)
    val pt = elaborateProtocols(ut.protocols, ut.model.methods)
    (Spec(ut.model, pt.toMap), ut.state)
  }

  case class ChiselImpl[M <: RawModule](instance: M, circuit: ir.Circuit, annos: Seq[Annotation])
  private def chiselElaborationImpl[M <: RawModule](gen: () => M): ChiselImpl[M] = {
    val (state, ip) = elaborate(gen)
    ChiselImpl(ip, state.circuit, state.annotations)
  }
  case class ChiselSpec[S <: UntimedModule](untimed: S, protos: Seq[Protocol], circuit: ir.Circuit, annos: Seq[Annotation])
  private def chiselElaborationSpec[S <: UntimedModule](gen: () => ProtocolSpec[S]): ChiselSpec[S] = {
    var ip: Option[ProtocolSpec[S]] = None
    val (state, _) = elaborate({() => ip = Some(gen()); ip.get.spec})
    ChiselSpec(ip.get.spec, ip.get.protos, state.circuit, state.annotations)
  }

  def apply[I <: RawModule, S <: UntimedModule](impl: () => I, proto: (I) => ProtocolSpec[S], findSubspecs: (I,S) => SubSpecs[I,S], inv: (I, S) => ProofCollateral[I, S]): VerificationProblem = {
    firrtlCompilerTime = 0L
    chiselElaborationTime = 0L
    val start = System.nanoTime()

    // Chisel elaboration for implementation and spec
    val implChisel = chiselElaborationImpl(impl)
    val specChisel = chiselElaborationSpec(() => proto(implChisel.instance))
    val subspecList = findSubspecs(implChisel.instance, specChisel.untimed).subspecs

    // Firrtl Compilation
    val implementation = elaborateImpl(implChisel, subspecList)
    val endImplementation = System.nanoTime()
    val (spec, untimed_state) = elaborateSpec(specChisel)
    val endSpec= System.nanoTime()

    // elaborate subspecs
    val implIo = (
      implementation.model.inputs.map(i => i.id -> i.typ) ++
        implementation.model.outputs.map(o => o._1 -> o._2.typ)).toMap
    val subspecs = subspecList.map { s =>
      val elaborated = chiselElaborationSpec(s.makeSpec)
      val (spec, _) = elaborateSpec[UntimedModule](elaborated)
      val instance = s.instance.module
      val prefixLength = instance.length + 1
      val io = implementation.submoduleIO.filter(_.startsWith(instance + "_")).map(_.substring(prefixLength))
      Subspec(instance, io.map(i => smt.Symbol(i, implIo(i))), spec, s.getBinding.map(_.module))
    }
    val endSubSpec= System.nanoTime()

    // elaborate the proof collateral
    val collateral = inv(implChisel.instance, specChisel.untimed)
    val mappings = elaborateMappings(implChisel.instance, implementation.state, specChisel.untimed, untimed_state, collateral.maps)
    val invariances = elaborateInvariances(implChisel.instance, implementation.state, collateral.invs)
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
      invariances = invariances,
      mapping = mappings
    )

    prob
  }
}