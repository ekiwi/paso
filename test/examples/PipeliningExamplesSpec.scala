package examples

import chisel3._
import chisel3.util._
import org.scalatest._
import paso._

class IdentityNoIdle[D <: Data](dataType: D) extends UntimedModule {
  val id = fun("id").in(dataType).out(dataType) { (in, out) => out := in }
}

class Register extends Module {
  val io = IO(new Bundle{
    val in = Input(UInt(32.W))
    val out = Output(UInt(32.W))
  })
  io.out := RegNext(io.in)
}

class RegisterProtocol(impl: Register) extends ProtocolSpec[IdentityNoIdle[UInt]] {
  val spec = new IdentityNoIdle[UInt](chiselTypeOf(impl.io.in))

  protocol(spec.id)(impl.io) { (clock, dut, in, out) =>
    dut.in.set(in)
    clock.step() // this is a short-hand for clock.stepAndFork() because we assert an output with no following step
    dut.out.expect(out)
  }
}

class Args2 extends Bundle { val a = UInt(32.W) ; val b = UInt(32.W) }
class Mul32Spec extends UntimedModule {
  val mul = fun("mul").in(new Args2).out(UInt(32.W)) { (in, out) => out := in.a * in.b }
}

class PipelinedMul extends Module {
  val io = IO(new Bundle{
    val a = Input(UInt(32.W))
    val b = Input(UInt(32.W))
    val out = Output(UInt(32.W))
  })
  io.out := RegNext(io.a * io.b)
}

class PipelinedMulProtocol(impl: PipelinedMul) extends ProtocolSpec[Mul32Spec] {
  val spec = new Mul32Spec

  protocol(spec.mul)(impl.io) { (clock, dut, in, out) =>
    dut.a.set(in.a)
    dut.b.set(in.b)
    clock.step() // this is a short-hand for clock.stepAndFork() because we assert an output with no following step
    dut.a.set(DontCare)
    dut.b.set(DontCare)
    dut.out.expect(out)
  }
}

class Args3 extends Bundle { val a = UInt(32.W) ; val b = UInt(32.W) ; val c = UInt(32.W) }
class Mac32Spec extends UntimedModule {
  val mac = fun("mac").in(new Args3).out(UInt(32.W)) { (in, out) =>
    out := in.a + in.b * in.c
  }
}

class MacIO extends Bundle{
  val a = Input(UInt(32.W))
  val b = Input(UInt(32.W))
  val c = Input(UInt(32.W))
  val out = Output(UInt(32.W))
}

class PipelinedMac extends Module {
  val io = IO(new MacIO)
  val mul = Module(new PipelinedMul)
  mul.io.a := io.b
  mul.io.b := io.c
  io.out := RegNext(io.a + mul.io.out)
}

// we put the common protocol into a trait to use it with different specs
trait MacProto extends ProtocolSpec[UntimedModule] {
  def proto(clock: Clock, dut: MacIO, in: Args3, out: UInt): Unit = {
    dut.b.set(in.b)
    dut.c.set(in.c)
    clock.step()

    dut.c.set(DontCare)
    dut.b.set(DontCare)
    dut.a.set(in.a)
    clock.step() // this is a short-hand for clock.stepAndFork() because we assert an output with no following step

    dut.a.set(DontCare)
    dut.out.expect(out)
  }
}


class PipelinedMacProtocol(impl: PipelinedMac) extends ProtocolSpec[Mac32Spec] with MacProto {
  val spec = new Mac32Spec
  protocol(spec.mac)(impl.io) { proto }
}


class Mac32SpecWithSubSpec extends UntimedModule {
  val multiplier = UntimedModule(new Mul32Spec)
  val mac = fun("mac").in(new Args3).out(UInt(32.W)) { (in, out) =>
    val m = Wire(new Args2) ; m.a := in.b ; m.b := in.c
    out := in.a + multiplier.mul(m)
  }
}

class PipelinedMacProtocolWithSubSpec(impl: PipelinedMac) extends ProtocolSpec[Mac32SpecWithSubSpec] with MacProto {
  val spec = new Mac32SpecWithSubSpec
  protocol(spec.mac)(impl.io) { proto }
}

class PipeliningExamplesSpec extends FlatSpec {
  "A simple register" should "refine its spec" in {
    Paso(new Register)(new RegisterProtocol(_)).proof()
  }

  "A pipelined 32-bit multiplier" should "refine its spec" in {
    Paso(new PipelinedMul)(new PipelinedMulProtocol(_)).proof()
  }

  "A pipelined 32-bit mac" should "refine its spec" in {
    Paso(new PipelinedMac)(new PipelinedMacProtocol(_)).proof()
  }

  "A pipelined 32-bit mac with abstract adder" should "refine its spec" in {
    Paso(new PipelinedMac)(new PipelinedMacProtocol(_))(new SubSpecs(_,_){
      replace(impl.mul)(new PipelinedMulProtocol(_))
    }).proof()
  }

  "A pipelined 32-bit mac with abstract adder and subspec" should "refine its spec" in {
    Paso(new PipelinedMac)(new PipelinedMacProtocolWithSubSpec(_))(new SubSpecs(_,_){
      replace(impl.mul)(new PipelinedMulProtocol(_)).bind(spec.multiplier)
    }).proof()
  }
}
