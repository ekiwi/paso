// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso

import chisel3._
import chisel3.hacks.elaborateInContextOfModule
import firrtl.annotations.Annotation
import firrtl.{ChirrtlForm, CircuitState, Compiler, CompilerUtils, HighFirrtlCompiler, HighFirrtlEmitter, HighForm, IRToWorkingIR, ResolveAndCheck, Transform, ir, passes}
import firrtl.ir
import uclid.smt

/** essentially a HighFirrtlCompiler + ToWorkingIR */
class CustomFirrtlCompiler extends Compiler {
  val emitter = new HighFirrtlEmitter
  def transforms: Seq[Transform] =
    CompilerUtils.getLoweringTransforms(ChirrtlForm, HighForm) ++
        Seq(new IRToWorkingIR, new ResolveAndCheck, new firrtl.transforms.DedupModules)
}

object FirrtlProtocolInterpreter {
  def run(circuit: ir.Circuit, annos: Seq[Annotation]): Unit ={
    val int = new ProtocolInterpreter
    new FirrtlProtocolInterpreter(circuit, annos, int).run()
    val graph = int.getGraph
    println(graph)
  }
}

/** protocols built on a custom extension of firrtl */
class FirrtlProtocolInterpreter(circuit: ir.Circuit, annos: Seq[Annotation], interpreter: ProtocolInterpreter) extends FirrtlInterpreter {
  require(circuit.modules.length == 1)
  require(circuit.modules.head.isInstanceOf[ir.Module])
  val mod = circuit.modules.head.asInstanceOf[ir.Module]
  val steps = annos.collect{ case StepAnnotation(target) => target.ref }.toSet
  val expects = annos.collect{ case ExpectAnnotation(target) => target.ref }.toSet

  def run(): Unit = onModule(mod)

  override def defWire(name: String, tpe: ir.Type): Unit = {
    if(steps.contains(name)) { interpreter.onStep() }
    super.defWire(name, tpe)
  }

  override def onConnect(name: String, expr: smt.Expr): Unit = {
    if(expects.contains(name)) expr match {
      case smt.OperatorApplication(smt.EqualityOp, List(lhs, rhs)) =>
        assert(isInput(lhs))
        interpreter.onExpect(lhs, rhs)
      case other => throw new RuntimeException(s"Unexpected pattern for expects: $other")
    } else if(name.startsWith("io_") && isOutput(name)) {
      interpreter.onSet(smt.Symbol(name, outputs(name)), expr)
    }
    super.onConnect(name, expr)
  }
}

object verify {
  def apply[IM <: RawModule, SM <: UntimedModule](impl: => IM, spec: => SM, bind: (IM, SM) => Binding[IM, SM]) = {

    def toFirrtl(gen: () => RawModule): (ir.Circuit, Seq[Annotation]) = {
      val chiselCircuit = Driver.elaborate(gen)
      val annos = chiselCircuit.annotations.map(_.toFirrtl)
      (Driver.toFirrtl(chiselCircuit), annos)
    }
    val highFirrtlCompiler = new CustomFirrtlCompiler
    def toHighFirrtl(c: ir.Circuit): ir.Circuit = {
      val st = highFirrtlCompiler.compile(CircuitState(c, ChirrtlForm, Seq(), None), Seq())
      val st_no_bundles = passes.LowerTypes.execute(st)
      st_no_bundles.circuit
    }

    def elaborateBody(m: RawModule, gen: () => Unit): ir.Statement =
      elaborateInContextOfModule(m, gen).modules.head.asInstanceOf[ir.Module].body

    var sp: Option[SM] = None
    val (main, _) = toFirrtl { () =>
      sp = Some(spec)
      sp.get
    }

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
    val impl_fir = toFirrtl{() => ip = Some(impl); ip.get}

    println("Implementation:")
    println(impl_fir._1.serialize)

    println()
    println("Binding...")
    val binding = bind(ip.get, sp.get)

    binding.protos.foreach{ p =>
      println(s"Protocol for: ${p.methodName}")
      val (raw_firrtl, annos) = toFirrtl(() => new MultiIOModule() { p.generate() })
      val ff = toHighFirrtl(raw_firrtl)
      FirrtlProtocolInterpreter.run(ff, annos)
      //println(ff.serialize)
      //println()
    }

    println("Mapping:")
    binding.maps.foreach { m =>
      val gen = {() => m(ip.get, sp.get)}
      val mod = elaborateInContextOfModule(ip.get, sp.get, "map", gen)
      val f = mod.modules.head.asInstanceOf[ir.Module].body
      println(f.serialize)
      println()
    }

    println("Invariances:")
    binding.invs.foreach { ii =>
      val gen = {() => ii(ip.get)}
      val mod = elaborateInContextOfModule(ip.get, gen)
      val f = mod.modules.head.asInstanceOf[ir.Module].body
      println(f.serialize)
      println()
    }

  }
}