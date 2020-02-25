package spec

import chisel3._
import chisel3.hacks.elaborateInContextOfModule
import chisel3.util._
import firrtl.ir
import impl.CircularPointerFifo
import org.scalatest._
import paso._



///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class UntimedFifo[G <: Data](val depth: Int, val dataType: G) extends UntimedModule {
  require(depth > 0)
  require(isPow2(depth))
  val mem = Reg(Vec(depth, dataType))
  val count = Reg(UInt((log2Ceil(depth) + 1).W))
  val read = Reg(UInt(log2Ceil(depth).W))
  val full = count === depth.U
  val empty = count === 0.U

  val push = fun("push").in(dataType).when(!full) { in =>
    mem(read + count) := in
    count := count + 1.U
  }

  val pop = fun("pop").out(dataType).when(!empty) { out =>
    out := mem(read)
    count := count - 1.U
    read := read + 1.U
  }

  val push_pop = fun("push_pop").in(dataType).out(dataType).when(!empty) { (in, out) =>
    mem(read + count) :=  in
    out := mem(read)
    read := read + 1.U
  }

  val idle = fun("idle")() // TODO: closing brackets are unfortunatelly required for method to be registered for now :(
}

class SpecBinding(impl: CircularPointerFifo, spec: UntimedFifo[UInt]) extends Binding(impl, spec) {
  // TODO: instantiate spec based on impl parametrization
  require(impl.width == spec.dataType.getWidth)
  require(impl.depth == spec.depth)

  // alternative which might be nicer as it would allow us to keep all of spec constant
  protocol(spec.push)(impl.io) { (dut, in) =>
    dut.pop.poke(false.B)
    dut.push.poke(true.B)
    dut.data_in.poke(in)
    dut.full.expect(false.B)
    step()
  }

  protocol(spec.pop)(impl.io) { (dut, out) =>
    dut.pop.poke(true.B)
    dut.push.poke(false.B)
    dut.data_out.expect(out)
    dut.empty.expect(false.B)
    step()
  }

  protocol(spec.push_pop)(impl.io) { (dut, in, out) =>
    dut.pop.poke(true.B)
    dut.push.poke(true.B)
    dut.data_in.poke(in)
    dut.data_out.expect(out)
    dut.empty.expect(false.B)
    step()
  }

  protocol(spec.idle)(impl.io) { dut =>
    dut.pop.poke(false.B)
    dut.push.poke(false.B)
    step()
  }

  mapping { (impl, spec) =>
    assert(spec.count === impl.cnt)
    assert(spec.read === impl.rdPtr)
    assert(spec.mem === impl.entries)
  }

  invariances { dut =>
    assert(dut.cnt <= dut.depth.U)
    assert(dut.rdPtr < dut.depth.U)
    assert(dut.wrPtr < dut.depth.U)
    when(dut.cnt === 0.U) {
      assert(dut.wrPtr === dut.rdPtr)
    } .elsewhen(dut.wrPtr > dut.rdPtr) {
      assert(dut.cnt === dut.wrPtr - dut.rdPtr)
    } .otherwise {
      assert(dut.cnt === dut.depth.U + dut.wrPtr - dut.rdPtr)
    }
  }
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class FifoSpec extends FlatSpec {
  val depth = 8
  val width = 8

  // Driver.execute(Array("--compiler", "mverilog"), () => new CircularPointerFifo(32, 32))

  def elaborate(gen: () => RawModule): ir.Circuit = Driver.toFirrtl(Driver.elaborate(gen))

  def elaborateBody(m: RawModule, gen: () => Unit): ir.Statement =
    elaborateInContextOfModule(m, gen).modules.head.asInstanceOf[ir.Module].body

  var spec: Option[UntimedFifo[UInt]] = None
  val main = elaborate { () =>
    spec = Some(new UntimedFifo(depth = depth, dataType = UInt(width.W)))
    spec.get
  }

  val methods = spec.get.methods.map { meth =>
    val body = elaborateBody(spec.get, meth.body.generate)
    val guard =  meth.guard.map(g => elaborateBody(spec.get, () => { val guard = g() }))
    (meth.name, guard, body)
  }

  println(main.serialize)
  methods.foreach{ case (name, guard, body) =>
    println(s"Method $name")
    guard.foreach{g => println(s"guard: ${g.serialize}")}
    println(body.serialize)
    println()}

  var impl: Option[CircularPointerFifo] = None
  val impl_fir = elaborate{() => impl = Some(new CircularPointerFifo(depth = depth, width = width) ); impl.get}

  println("Implementation:")
  println(impl_fir.serialize)

  println()
  println("Binding...")
  val binding = new SpecBinding(impl.get, spec.get)

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
    val gen = {() => m(impl.get, spec.get)}
    val mod = elaborateInContextOfModule(impl.get, spec.get, "map", gen)
    val f = mod.modules.head.asInstanceOf[ir.Module].body
    println(f.serialize)
    println()
  }

  println("Invariances:")
  binding.invs.foreach { ii =>
    val gen = {() => ii(impl.get)}
    val mod = elaborateInContextOfModule(impl.get, gen)
    val f = mod.modules.head.asInstanceOf[ir.Module].body
    println(f.serialize)
    println()
  }

}
