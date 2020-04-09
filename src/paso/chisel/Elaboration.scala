// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import chisel3.{Driver, MultiIOModule, RawModule}
import chisel3.hacks.elaborateInContextOfModule
import firrtl.annotations.Annotation
import firrtl.ir.{BundleType, NoInfo}
import firrtl.{ChirrtlForm, CircuitState, Compiler, CompilerUtils, HighFirrtlCompiler, HighFirrtlEmitter, HighForm, IRToWorkingIR, LowFirrtlCompiler, ResolveAndCheck, Transform, ir, passes}
import paso.verification.{Assertion, MethodSemantics, NamedExpr, PendingInputNode, ProtocolInterpreter, UntimedModel, VerificationGraph, VerificationProblem}
import paso.{Binding, UntimedModule}
import uclid.smt

/** essentially a HighFirrtlCompiler + ToWorkingIR */
class CustomFirrtlCompiler extends Compiler {
  val emitter = new HighFirrtlEmitter
  def transforms: Seq[Transform] =
    CompilerUtils.getLoweringTransforms(ChirrtlForm, HighForm) ++
        Seq(new IRToWorkingIR, new ResolveAndCheck, new firrtl.transforms.DedupModules)
}



object Elaboration {
  private def toFirrtl(gen: () => RawModule): (ir.Circuit, Seq[Annotation]) = {
    val chiselCircuit = Driver.elaborate(gen)
    val annos = chiselCircuit.annotations.map(_.toFirrtl)
    (Driver.toFirrtl(chiselCircuit), annos)
  }
  private val highFirrtlCompiler = new CustomFirrtlCompiler
  private def toHighFirrtl(c: ir.Circuit, annos: Seq[Annotation] = Seq()): (ir.Circuit, Seq[Annotation]) = {
    val st = highFirrtlCompiler.compile(CircuitState(c, ChirrtlForm, annos, None), Seq())
    (st.circuit, st.annotations)
  }
  private def lowerTypes(tup: (ir.Circuit, Seq[Annotation])): (ir.Circuit, Seq[Annotation]) = {
    val st = CircuitState(tup._1, ChirrtlForm, tup._2, None)
    // TODO: we would like to lower bundles but not vecs ....
    val st_no_bundles = passes.LowerTypes.runTransform(st)
    (st_no_bundles.circuit, st_no_bundles.annotations)
  }
  private val lowFirrtlCompiler = new LowFirrtlCompiler
  private def toLowFirrtl(c: ir.Circuit, annos: Seq[Annotation] = Seq()): (ir.Circuit, Seq[Annotation]) = {
    val st = lowFirrtlCompiler.compile(CircuitState(c, ChirrtlForm, annos, None), Seq())
    (st.circuit, st.annotations)
  }
  private def getMain(c: ir.Circuit): ir.Module = c.modules.find(_.name == c.main).get.asInstanceOf[ir.Module]

  private def elaborateMappings[IM <: RawModule, SM <: UntimedModule](
      impl: IM, impl_state: Seq[State],
      spec: SM, spec_state: Seq[State], maps: Seq[(IM, SM) => Unit]): Seq[Assertion] = {
    val map_ports = impl_state.map { st =>
      ir.Port(NoInfo, impl.name + "." + st.name, ir.Input, st.tpe)
    } ++ spec_state.map { st =>
      ir.Port(NoInfo, spec.name + "." + st.name, ir.Input, st.tpe)
    }
    val map_mod = ir.Module(NoInfo, name = "m", ports=map_ports, body=ir.EmptyStmt)

    maps.flatMap { m =>
      val mod = elaborateInContextOfModule(impl, spec, "map", {() => m(impl, spec)})
      val body = mod._1.modules.head.asInstanceOf[ir.Module].body
      val c = ir.Circuit(NoInfo, Seq(map_mod.copy(body=body)), map_mod.name)
      //val elaborated = lowerTypes(toHighFirrtl(c, mod._2))
      val elaborated = toHighFirrtl(c, mod._2)
      new FirrtlInvarianceInterpreter(elaborated._1, elaborated._2).run().asserts
    }
  }

  private def elaborateInvariances[IM <: RawModule](impl: IM, impl_state: Seq[State], invs: Seq[IM => Unit]): Seq[Assertion] = {
    val inv_ports = impl_state.map { st =>
      ir.Port(NoInfo, st.name, ir.Input, st.tpe)
    }
    val inv_mod = ir.Module(NoInfo, name = "i", ports=inv_ports, body=ir.EmptyStmt)

    invs.flatMap { ii =>
      val mod = elaborateInContextOfModule(impl, {() => ii(impl)})
      val body = mod._1.modules.head.asInstanceOf[ir.Module].body
      val c = ir.Circuit(NoInfo, Seq(inv_mod.copy(body=body)), inv_mod.name)
      val elaborated = lowerTypes(toHighFirrtl(c, mod._2))
      new FirrtlInvarianceInterpreter(elaborated._1, elaborated._2).run().asserts
    }
  }

  private def elaborateProtocols(protos: Seq[paso.Protocol], methods: Map[String, MethodSemantics]): Seq[(String, PendingInputNode)] = {
    protos.map{ p =>
      //println(s"Protocol for: ${p.methodName}")
      val (raw_firrtl, raw_annos) = toFirrtl(() => new MultiIOModule() { p.generate(p.methodName + "_", clock) })
      val (ff, annos) = lowerTypes(toHighFirrtl(raw_firrtl, raw_annos))
      val int = new ProtocolInterpreter(enforceNoInputAfterOutput = false)
      //println(ff.serialize)
      new FirrtlProtocolInterpreter(p.methodName, ff, annos, int).run()
      (p.methodName, int.getGraph(p.methodName, methods(p.methodName).guard))
    }
  }

  private case class Impl[IM <: RawModule](mod: IM, state: Seq[State], model: smt.TransitionSystem)
  private def elaborateImpl[IM <: RawModule](impl: => IM): Impl[IM] = {
    var ip: Option[IM] = None
    val (impl_c, impl_anno) = toFirrtl({() => ip = Some(impl); ip.get})
    val impl_fir = toHighFirrtl(impl_c, impl_anno)._1
    val impl_state = FindState(impl_fir).run()
    val impl_model = FirrtlToFormal(impl_fir, impl_anno)

    //println("State extracted from Chisel")
    //impl_state.foreach(st => println(s"${st.name}: ${st.tpe}"))
    //println("State extracted from BTOR")
    //impl_model.states.foreach(st => println(s"${st.sym.id} : ${st.sym.typ}"))

    // cross check states:
    impl_state.foreach { state =>
      if(!impl_model.states.exists(_.sym.id == state.name)) {
        if(state.tpe.isInstanceOf[BundleType]) {
          println(s"WARN: todo, deal with bundle states ($state)")
        } else {
          println(s"WARN: State $state is missing from the formal model!")
        }
      }
      //assert(impl_model.states.exists(_.sym.id == state.name), s"State $state is missing from the formal model!")
    }
    Impl(ip.get, impl_state, impl_model)
  }

  private case class Spec[SM <: UntimedModule](mod: SM, state: Seq[State], model: UntimedModel)
  private def elaborateSpec[SM <: UntimedModule](spec: => SM) = {
    var sp: Option[SM] = None
    val (main, _) = toFirrtl { () =>
      sp = Some(spec)
      sp.get
    }

    val spec_name = main.main
    val spec_state = FindState(main).run()

    val spec_module = getMain(main)
    val methods = sp.get.methods.map { meth =>
      val (raw_firrtl, raw_annos) = elaborateInContextOfModule(sp.get, meth.generate)

      // build module for this method:
      val method_body = getMain(raw_firrtl).body
      val comb_body = ir.Block(Seq(spec_module.body, method_body))
      val comb_ports = spec_module.ports ++ getMain(raw_firrtl).ports
      val comb_c = ir.Circuit(NoInfo, Seq(spec_module.copy(ports=comb_ports, body=comb_body)), spec_name)

      // compile combined module down to low firrtl
      val (ff, annos) = toLowFirrtl(comb_c, raw_annos)
      val semantics = new FirrtlUntimedMethodInterpreter(ff, annos).run().getSemantics
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
    val untimed_model = UntimedModel(name = spec_name, state = spec_smt_state, methods = methods)
    Spec(sp.get, spec_state, untimed_model)
  }

  def apply[IM <: RawModule, SM <: UntimedModule](impl: => IM, spec: => SM, bind: (IM, SM) => Binding[IM, SM]): VerificationProblem = {

    val implementation = elaborateImpl(impl)
    val untimed = elaborateSpec(spec)

    // elaborate the binding
    val binding = bind(implementation.mod, untimed.mod)
    val protos = elaborateProtocols(binding.protos, untimed.model.methods)
    val mappings = elaborateMappings(implementation.mod, implementation.state, untimed.mod, untimed.state, binding.maps)
    val invariances = elaborateInvariances(implementation.mod, implementation.state, binding.invs)

    // combine into verification problem
    val prob = VerificationProblem(
      impl = implementation.model,
      untimed = untimed.model,
      protocols = protos.toMap,
      invariances = invariances,
      mapping = mappings
    )

    prob
  }
}