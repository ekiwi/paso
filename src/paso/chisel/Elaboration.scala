// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import chisel3._
import chisel3.hacks.elaborateInContextOfModule
import firrtl.annotations.Annotation
import firrtl.ir.NoInfo
import firrtl.{ChirrtlForm, CircuitState, Compiler, CompilerUtils, HighFirrtlEmitter, HighForm, IRToWorkingIR, ResolveAndCheck, Transform, ir, passes}
import paso.{Binding, UntimedModule}

/** essentially a HighFirrtlCompiler + ToWorkingIR */
class CustomFirrtlCompiler extends Compiler {
  val emitter = new HighFirrtlEmitter
  def transforms: Seq[Transform] =
    CompilerUtils.getLoweringTransforms(ChirrtlForm, HighForm) ++
        Seq(new IRToWorkingIR, new ResolveAndCheck, new firrtl.transforms.DedupModules)
}

object Elaboration {
  def apply[IM <: RawModule, SM <: UntimedModule](impl: => IM, spec: => SM, bind: (IM, SM) => Binding[IM, SM]) = {

    def toFirrtl(gen: () => RawModule): (ir.Circuit, Seq[Annotation]) = {
      val chiselCircuit = Driver.elaborate(gen)
      val annos = chiselCircuit.annotations.map(_.toFirrtl)
      (Driver.toFirrtl(chiselCircuit), annos)
    }
    val highFirrtlCompiler = new CustomFirrtlCompiler
    def toHighFirrtl(c: ir.Circuit, annos: Seq[Annotation] = Seq()): (ir.Circuit, Seq[Annotation]) = {
      val st = highFirrtlCompiler.compile(CircuitState(c, ChirrtlForm, annos, None), Seq())
      val st_no_bundles = passes.LowerTypes.execute(st)
      (st_no_bundles.circuit, st_no_bundles.annotations)
    }

    def elaborateBody(m: RawModule, gen: () => Unit): ir.Statement =
      elaborateInContextOfModule(m, gen)._1.modules.head.asInstanceOf[ir.Module].body

    var sp: Option[SM] = None
    val (main, _) = toFirrtl { () =>
      sp = Some(spec)
      sp.get
    }

    val spec_state = FindState(main).run()
    spec_state.foreach(println)

    val methods = sp.get.methods.map { meth =>
      val body = elaborateBody(sp.get, meth.body.generate)
      val guard =  meth.guard.map(g => elaborateBody(sp.get, () => { val guard = g() }))
      (meth.name, guard, body)
    }

    println(main.serialize)
    methods.foreach{ case (name, guard, body) =>
      println(s"Method $name")
      guard.foreach{g => println(s"guard: ${g.serialize}")}
      println(body.serialize)
      println()}

    var ip: Option[IM] = None
    val (impl_c, impl_anno) = toFirrtl({() => ip = Some(impl); ip.get})
    val impl_fir = toHighFirrtl(impl_c, impl_anno)._1
    val impl_name = impl_fir.main

    println("Implementation:")
    println(impl_fir.serialize)

    val impl_state = FindState(impl_fir).run()
    impl_state.foreach(println)

    println()
    println("Binding...")
    val binding = bind(ip.get, sp.get)

    binding.protos.foreach{ p =>
      println(s"Protocol for: ${p.methodName}")
      val (raw_firrtl, raw_annos) = toFirrtl(() => new MultiIOModule() { p.generate() })
      val (ff, annos) = toHighFirrtl(raw_firrtl, raw_annos)
      FirrtlProtocolInterpreter.run(ff, annos)
      //println(ff.serialize)
      //println()
    }

    println("Mapping:")
    binding.maps.foreach { m =>
      val gen = {() => m(ip.get, sp.get)}
      println()
      val mod = elaborateInContextOfModule(ip.get, sp.get, "map", gen)
      val f = mod._1.modules.head.asInstanceOf[ir.Module].body
      println(f.serialize)
      println()
    }

    println("Invariances:")
    val inv_ports = impl_state.map { case (name, tpe) =>
      ir.Port(NoInfo, name, ir.Input, tpe)
    }
    val inv_mod = ir.Module(NoInfo, name = "i", ports=inv_ports, body=ir.EmptyStmt)


    binding.invs.foreach { ii =>
      val gen = {() => ii(ip.get)}
      val mod = elaborateInContextOfModule(ip.get, gen)
      val body = mod._1.modules.head.asInstanceOf[ir.Module].body
      val c = ir.Circuit(NoInfo, Seq(inv_mod.copy(body=body)), inv_mod.name)
      val elaborated = toHighFirrtl(c, mod._2)
      val invariances = new FirrtlInvarianceInterpreter(elaborated._1, elaborated._2).run().asserts
      invariances.foreach(println)
      println()
    }

  }
}