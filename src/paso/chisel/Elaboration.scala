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
    val st_no_bundles = passes.LowerTypes.execute(st)
    (st_no_bundles.circuit, st_no_bundles.annotations)
  }
  private def elaborateBody(m: RawModule, gen: () => Unit): ir.Statement =
    elaborateInContextOfModule(m, gen)._1.modules.head.asInstanceOf[ir.Module].body


  private def getMain(c: ir.Circuit): ir.Module = c.modules.find(_.name == c.main).get.asInstanceOf[ir.Module]

  def apply[IM <: RawModule, SM <: UntimedModule](impl: => IM, spec: => SM, bind: (IM, SM) => Binding[IM, SM]) = {

    println("Implementation:")
    var ip: Option[IM] = None
    val (impl_c, impl_anno) = toFirrtl({() => ip = Some(impl); ip.get})
    val impl_fir = toHighFirrtl(impl_c, impl_anno)._1
    val impl_name = impl_fir.main
    val impl_state = FindState(impl_fir).run()
    val impl_model = FirrtlToFormal(impl_fir, impl_anno)
    // cross check states:
    impl_state.foreach { case (name, tpe) =>
      assert(impl_model.states.exists(_.sym.id == name), s"State $name : $tpe is missing from the formal model!")
    }

    println()
    println("Untimed Model:")
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
      val comb_c = ir.Circuit(NoInfo, Seq(spec_module.copy(body=comb_body)), spec_name)


      println(comb_c.serialize)

      val (ff, annos) = toHighFirrtl(comb_c, raw_annos)

      println(meth.name)
      println(ff.serialize)


      val interpreter = new FirrtlUntimedMethodInterpreter(ff, annos).run()

      println()
      //val body = elaborateBody(sp.get, meth.generate)
      //(meth.name, body)
    }

//    println(main.serialize)
//    methods.foreach{ case (name, body) =>
//      println(s"Method $name")
//      println(body.serialize)
//      println()
//    }


    println()
    println("Binding...")
    val binding = bind(ip.get, sp.get)

    binding.protos.foreach{ p =>
      println(s"Protocol for: ${p.methodName}")
      val (raw_firrtl, raw_annos) = toFirrtl(() => new MultiIOModule() { p.generate() })
      val (ff, annos) = lowerTypes(toHighFirrtl(raw_firrtl, raw_annos))
      FirrtlProtocolInterpreter.run(ff, annos)
    }

    println("Mapping:")
    val map_ports = impl_state.map { case (name, tpe) =>
      ir.Port(NoInfo, impl_name + "." + name, ir.Input, tpe)
    } ++ spec_state.map { case (name, tpe) =>
      ir.Port(NoInfo, spec_name + "." + name, ir.Input, tpe)
    }
    val map_mod = ir.Module(NoInfo, name = "m", ports=map_ports, body=ir.EmptyStmt)

    val mappings: Seq[Assertion] = binding.maps.flatMap { m =>
      val gen = {() => m(ip.get, sp.get)}
      val mod = elaborateInContextOfModule(ip.get, sp.get, "map", gen)
      val body = mod._1.modules.head.asInstanceOf[ir.Module].body
      val c = ir.Circuit(NoInfo, Seq(map_mod.copy(body=body)), map_mod.name)
      val elaborated = lowerTypes(toHighFirrtl(c, mod._2))
      new FirrtlInvarianceInterpreter(elaborated._1, elaborated._2).run().asserts
    }
    mappings.foreach(println)

    println()
    println("Invariances:")
    val inv_ports = impl_state.map { case (name, tpe) =>
      ir.Port(NoInfo, name, ir.Input, tpe)
    }
    val inv_mod = ir.Module(NoInfo, name = "i", ports=inv_ports, body=ir.EmptyStmt)


    val invariances: Seq[Assertion] = binding.invs.flatMap { ii =>
      val gen = {() => ii(ip.get)}
      val mod = elaborateInContextOfModule(ip.get, gen)
      val body = mod._1.modules.head.asInstanceOf[ir.Module].body
      val c = ir.Circuit(NoInfo, Seq(inv_mod.copy(body=body)), inv_mod.name)
      val elaborated = lowerTypes(toHighFirrtl(c, mod._2))
      new FirrtlInvarianceInterpreter(elaborated._1, elaborated._2).run().asserts
    }
    invariances.foreach(println)

  }
}