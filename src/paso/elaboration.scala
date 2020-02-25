// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso

import chisel3._
import chisel3.hacks.elaborateInContextOfModule
import firrtl.ir

object verify {
  def apply[IM <: RawModule, SM <: UntimedModule](impl: => IM, spec: => SM, bind: (IM, SM) => Binding[IM, SM]) = {

    def elaborate(gen: () => RawModule): ir.Circuit = Driver.toFirrtl(Driver.elaborate(gen))

    def elaborateBody(m: RawModule, gen: () => Unit): ir.Statement =
      elaborateInContextOfModule(m, gen).modules.head.asInstanceOf[ir.Module].body

    var sp: Option[SM] = None
    val main = elaborate { () =>
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
    val impl_fir = elaborate{() => ip = Some(impl); ip.get}

    println("Implementation:")
    println(impl_fir.serialize)

    println()
    println("Binding...")
    val binding = bind(ip.get, sp.get)

    // try to elaborate thing in the binding
    def elaborate_protocol(p: Protocol) = {
      elaborate(() => new MultiIOModule() { p.generate() }).modules.head.asInstanceOf[ir.Module].body
    }

    binding.protos.foreach{ p =>
      println(s"Protocol for: ${p.methodName}")
      val ff = elaborate_protocol(p)
      println(ff.serialize)
      println()
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