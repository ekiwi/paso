package examples

import chisel3._
import chisel3.util._
import org.scalatest.flatspec.AnyFlatSpec
import paso._

class IdentityNoIdle[D <: Data](dataType: D) extends UntimedModule {
  val id = fun("id").in(dataType).out(dataType) { (in, out) => out := in }
}

class Register(withBug: Boolean = false) extends Module {
  val io = IO(new Bundle{
    val in = Input(UInt(32.W))
    val out = Output(UInt(32.W))
  })
  if(withBug) {
    io.out := RegNext(Mux(io.in === 0.U, 1.U, io.in))
  } else {
    io.out := RegNext(io.in)
  }
}

class RegisterProtocol(impl: Register) extends ProtocolSpec[IdentityNoIdle[UInt]] {
  val spec = new IdentityNoIdle[UInt](chiselTypeOf(impl.io.in))

  protocol(spec.id)(impl.io) { (clock, dut, in, out) =>
    dut.in.set(in)
    clock.stepAndFork()
    dut.in.set(DontCare)
    dut.out.expect(out)
    clock.step()
  }
}

class Args2 extends Bundle { val a = UInt(32.W) ; val b = UInt(32.W) }
class Mul32Spec extends UntimedModule {
  val mul = fun("mul").in(new Args2).out(UInt(32.W)) { (in, out) => out := in.a * in.b }
}

class PipelinedMul(withBug: Boolean = false) extends Module {
  val io = IO(new Bundle{
    val a = Input(UInt(32.W))
    val b = Input(UInt(32.W))
    val out = Output(UInt(32.W))
  })
  if(withBug) {
    io.out := RegNext(io.a - io.b)
  } else {
    io.out := RegNext(io.a * io.b)
  }
}

class PipelinedMulProtocol(impl: PipelinedMul) extends ProtocolSpec[Mul32Spec] {
  val spec = new Mul32Spec

  protocol(spec.mul)(impl.io) { (clock, dut, in, out) =>
    dut.a.set(in.a)
    dut.b.set(in.b)
    clock.stepAndFork()
    dut.a.set(DontCare)
    dut.b.set(DontCare)
    dut.out.expect(out)
    clock.step()
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

class PipelinedMac(withBug: Boolean = false) extends Module {
  val io = IO(new MacIO)
  val mul = Module(new PipelinedMul)
  mul.io.a := io.b
  mul.io.b := (if(withBug) io.b else io.c)
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
    clock.stepAndFork()

    dut.a.set(DontCare)
    dut.out.expect(out)
    clock.step()
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

class Add2Spec extends UntimedModule {
  val add = fun("add").in(new Args2).out(UInt(32.W)) { (in, out) =>
    out := in.a + in.b
  }
}

class PipelinedAdd2(withBug: Boolean = false) extends Module {
  val io = IO(new Bundle{
    val a = Input(UInt(32.W))
    val b = Input(UInt(32.W))
    val out = Output(UInt(32.W))
  })
  if(withBug) {
    io.out := RegNext(io.a - io.b)
  } else {
    io.out := RegNext(io.a + io.b)
  }
}

class PipelinedAdd2Protocol(impl: PipelinedAdd2) extends ProtocolSpec[Add2Spec] {
  val spec = new Add2Spec

  protocol(spec.add)(impl.io) { (clock, dut, in, out) =>
    dut.a.set(in.a)
    dut.b.set(in.b)
    clock.stepAndFork()
    dut.a.set(DontCare)
    dut.b.set(DontCare)
    dut.out.expect(out)
    clock.step()
  }
}

class PipelinedAdd3(withBug: Boolean = false) extends Module {
  val io = IO(new Bundle{
    val a = Input(UInt(32.W))
    val b = Input(UInt(32.W))
    val c = Input(UInt(32.W))
    val out = Output(UInt(32.W))
  })
  val a = Seq.tabulate(2)(_ => Module(new PipelinedAdd2))
  a(0).io.a := io.a
  a(0).io.b := (if(withBug) io.a else io.b)
  a(1).io.a := a(0).io.out
  a(1).io.b := io.c
  io.out := a(1).io.out
}

class Add3Spec extends UntimedModule {
  val add3 = fun("add3").in(new Args3).out(UInt(32.W)) { (in, out) =>
    out := in.a + in.b + in.c
  }
}

class Add3CompositionalSpec extends UntimedModule {
  val add2 = UntimedModule(new Add2Spec)
  val add3 = fun("add3").in(new Args3).out(UInt(32.W)) { (in, out) =>
    val a0 = Wire(new Args2)
    a0.a := in.a
    a0.b := in.b
    val a1 = Wire(new Args2)
    a1.a := add2.add(a0)
    a1.b := in.c
    out := add2.add(a1)
  }
}

class PipelinedAdd3Protocol(impl: PipelinedAdd3) extends ProtocolSpec[Add3Spec] {
  val spec = new Add3Spec

  protocol(spec.add3)(impl.io) { (clock, dut, in, out) =>
    dut.a.set(in.a)
    dut.b.set(in.b)
    clock.step()
    dut.a.set(DontCare)
    dut.b.set(DontCare)
    dut.c.set(in.c)
    clock.stepAndFork()
    dut.c.set(DontCare)
    dut.out.expect(out)
    clock.step()
  }
}

class PipelinedAdd3CompositionalProtocol(impl: PipelinedAdd3) extends ProtocolSpec[Add3CompositionalSpec] {
  val spec = new Add3CompositionalSpec

  protocol(spec.add3)(impl.io) { (clock, dut, in, out) =>
    dut.a.set(in.a)
    dut.b.set(in.b)
    clock.step()
    dut.a.set(DontCare)
    dut.b.set(DontCare)
    dut.c.set(in.c)
    clock.stepAndFork()
    dut.c.set(DontCare)
    dut.out.expect(out)
    clock.step()
  }
}

class PipelinedAdd3Delay2(withBug: Boolean = false) extends Module {
  val io = IO(new Bundle{
    val first = Input(Bool())
    val a = Input(UInt(32.W))
    val b = Input(UInt(32.W))
    val out = Output(UInt(32.W))
  })
  val a = Module(new PipelinedAdd2)
  a.io.a := (if(withBug) io.a else Mux(io.first, io.a, a.io.out))
  a.io.b := io.b
  io.out := a.io.out
}

class PipelinedAdd3Delay2Protocol(impl: PipelinedAdd3Delay2) extends ProtocolSpec[Add3Spec] {
  val spec = new Add3Spec

  protocol(spec.add3)(impl.io) { (clock, dut, in, out) =>
    dut.first.set(true.B)
    dut.a.set(in.a)
    dut.b.set(in.b)
    clock.step()
    dut.first.set(false.B)
    dut.a.set(DontCare)
    dut.b.set(in.c)
    clock.stepAndFork()
    dut.first.set(DontCare)
    dut.b.set(DontCare)
    dut.out.expect(out)
    clock.step()
  }
}

class PipelinedAdd3Delay2ProtocolCompisitional(impl: PipelinedAdd3Delay2) extends ProtocolSpec[Add3CompositionalSpec] {
  val spec = new Add3CompositionalSpec

  protocol(spec.add3)(impl.io) { (clock, dut, in, out) =>
    dut.first.set(true.B)
    dut.a.set(in.a)
    dut.b.set(in.b)
    clock.step()
    dut.first.set(false.B)
    dut.a.set(DontCare)
    dut.b.set(in.c)
    clock.stepAndFork()
    dut.first.set(DontCare)
    dut.b.set(DontCare)
    dut.out.expect(out)
    clock.step()
  }
}

class PipeliningExamplesSpec extends AnyFlatSpec with PasoTester {
  "A simple register" should "refine its spec" in {
    test(new Register)(new RegisterProtocol(_)).proof()
  }

  "A simple register" should "refine its spec (using the isolated method strategy)" in {
    val opt = Paso.Default.copy(strategy = ProofIsolatedMethods)
    test(new Register)(new RegisterProtocol(_)).proof(opt)
  }

  "A simple register" should "pass random testing" in {
    test(new Register)(new RegisterProtocol(_)).randomTest(10)
  }

  "A simple register with bug" should "fail" in {
    val fail = intercept[AssertionError] {
      test(new Register(withBug = true))(new RegisterProtocol(_)).proof()
    }
    assert(fail.getMessage.contains("Failed to proof Register correct"))
  }

  "A simple register with bug" should "fail (using the isolated method strategy)" in {
    val opt = Paso.Default.copy(strategy = ProofIsolatedMethods)
    val fail = intercept[AssertionError] {
      test(new Register(withBug = true))(new RegisterProtocol(_)).proof(opt)
    }
    assert(fail.getMessage.contains("Failed to proof Register correct"))
  }

  "A pipelined 32-bit adder" should "refine its spec" in {
    test(new PipelinedAdd2)(new PipelinedAdd2Protocol(_)).proof()
  }

  "A pipelined 32-bit adder with bug" should "fail" in {
    val fail = intercept[AssertionError] {
      test(new PipelinedAdd2(withBug = true))(new PipelinedAdd2Protocol(_)).proof()
    }
    assert(fail.getMessage.contains("Failed to proof PipelinedAdd2 correct"))
  }

  "A pipelined 32-bit add3" should "refine its spec" in {
    test(new PipelinedAdd3)(new PipelinedAdd3Protocol(_)).proof()
  }

  "A pipelined 32-bit add3 with abstract add2" should "refine its spec" in {
    test(new PipelinedAdd3)(new PipelinedAdd3Protocol(_))(new SubSpecs(_, _) {
      impl.a.foreach(a => replace(a)(new PipelinedAdd2Protocol(_)))
    }).proof()
  }

  "A pipelined 32-bit add3 with abstract add2 and compositional spec" should "refine its spec" in {
    test(new PipelinedAdd3)(new PipelinedAdd3CompositionalProtocol(_))(new SubSpecs(_, _) {
      impl.a.foreach(a => replace(a)(new PipelinedAdd2Protocol(_)))
    }).proof()
  }

  "A pipelined 32-bit add3 with abstract and bound add2 and compositional spec" should "refine its spec" in {
    test(new PipelinedAdd3)(new PipelinedAdd3CompositionalProtocol(_))(new SubSpecs(_, _) {
      impl.a.foreach(a => replace(a)(new PipelinedAdd2Protocol(_)).bind(spec.add2))
    }).proof(Paso.MCYices2)
  }

  "A pipelined 32-bit add3 with bug" should "fail" in {
    val fail = intercept[AssertionError] {
      test(new PipelinedAdd3(withBug = true))(new PipelinedAdd3Protocol(_)).proof()
    }
    assert(fail.getMessage.contains("Failed to proof PipelinedAdd3 correct"))
  }

  "A pipelined 32-bit add3 with delay=2" should "refine its spec" in {
    test(new PipelinedAdd3Delay2())(new PipelinedAdd3Delay2Protocol(_)).proof()
  }

  "A pipelined 32-bit add3 with delay=2 with abstract add2" should "refine its spec" in {
    test(new PipelinedAdd3Delay2())(new PipelinedAdd3Delay2Protocol(_))(new SubSpecs(_, _) {
      replace(impl.a)(new PipelinedAdd2Protocol(_))
    }).proof()
  }

  "A pipelined 32-bit add3 with delay=2 with abstract add2 and compositional spec" should "refine its spec" in {
    test(new PipelinedAdd3Delay2())(new PipelinedAdd3Delay2ProtocolCompisitional(_))(new SubSpecs(_, _) {
      replace(impl.a)(new PipelinedAdd2Protocol(_))
    }).proof()
  }

  "A pipelined 32-bit add3 with delay=2 with abstract and bound add2 and compositional spec" should "refine its spec" in {
    test(new PipelinedAdd3Delay2())(new PipelinedAdd3Delay2ProtocolCompisitional(_))(new SubSpecs(_, _) {
      replace(impl.a)(new PipelinedAdd2Protocol(_)).bind(spec.add2)
    }).proof(Paso.MCYices2)
  }

  "A pipelined 32-bit add3 with delay=2 with bug" should "fail" in {
    val fail = intercept[AssertionError] {
      test(new PipelinedAdd3Delay2(withBug = true))(new PipelinedAdd3Delay2Protocol(_)).proof()
    }
    assert(fail.getMessage.contains("Failed to proof PipelinedAdd3Delay2 correct"))
  }
}

// the multiplication makes some of the SMT solvers struggle...
class PipeliningExamplesWithMulSpec extends AnyFlatSpec with PasoTester {
  "A pipelined 32-bit multiplier" should "refine its spec" in {
    test(new PipelinedMul)(new PipelinedMulProtocol(_)).proof()
  }

  "A pipelined 32-bit multiplier with bug" should "fail" in {
    val fail = intercept[AssertionError] {
      test(new PipelinedMul(withBug = true))(new PipelinedMulProtocol(_)).proof()
    }
    assert(fail.getMessage.contains("Failed to proof PipelinedMul correct"))
  }

  "A pipelined 32-bit multiplier with bug" should "fail bmc" in {
    val fail = intercept[AssertionError] {
      test(new PipelinedMul(withBug = true))(new PipelinedMulProtocol(_)).bmc(1)
    }
    assert(fail.getMessage.contains("Found a disagreement between implementation and spec."))
  }

  "A pipelined 32-bit mac" should "refine its spec" in {
    test(new PipelinedMac)(new PipelinedMacProtocol(_)).proof()
  }

  "A pipelined 32-bit mac with bug" should "fail" in {
    val fail = intercept[AssertionError] {
      test(new PipelinedMac(withBug = true))(new PipelinedMacProtocol(_)).proof()
    }
    assert(fail.getMessage.contains("Failed to proof PipelinedMac correct"))
  }

  "A pipelined 32-bit mac with abstract adder" should "refine its spec" in {
    test(new PipelinedMac)(new PipelinedMacProtocol(_))(new SubSpecs(_,_){
      replace(impl.mul)(new PipelinedMulProtocol(_))
    }).proof()
  }

  "A pipelined 32-bit mac with abstract adder with bug" should "fail" in {
    val fail = intercept[AssertionError] {
      test(new PipelinedMac(withBug = true))(new PipelinedMacProtocol(_))(new SubSpecs(_, _) {
        replace(impl.mul)(new PipelinedMulProtocol(_))
      }).proof()
    }
    assert(fail.getMessage.contains("Failed to proof PipelinedMac correct"))
  }

  "A pipelined 32-bit mac with abstract adder and subspec" should "refine its spec" in {
    test(new PipelinedMac)(new PipelinedMacProtocolWithSubSpec(_))(new SubSpecs(_,_){
      replace(impl.mul)(new PipelinedMulProtocol(_)).bind(spec.multiplier)
    }).proof(Paso.MCYices2)
  }

  "A pipelined 32-bit mac with abstract adder and subspec with bug" should "fail" in {
    // TODO: once the witness generation for UFs is implemented, this should be changed to an AssertionError
    assertThrows[NotImplementedError] {
      test(new PipelinedMac(withBug = true))(new PipelinedMacProtocolWithSubSpec(_))(new SubSpecs(_, _) {
        replace(impl.mul)(new PipelinedMulProtocol(_)).bind(spec.multiplier)
      }).proof(Paso.MCYices2)
    }
  }
}
