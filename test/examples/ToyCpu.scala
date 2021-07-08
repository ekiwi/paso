package examples

import chisel3._
import chisel3.experimental.{ChiselAnnotation, annotate}
import chisel3.util._
import firrtl.annotations.MemoryScalarInitAnnotation
import org.scalatest.flatspec.AnyFlatSpec
import paso._

class ToyCpuSpec extends AnyFlatSpec with PasoTester {
  behavior of "ToyCpu"

  it should "pass some cycles of BMC" in {
    test(new ToyCpu)(new ToyCpuProtocols(_)).bmc(4)
  }

  it should "pass some cycles of random testing" in {
    test(new ToyCpu)(new ToyCpuProtocols(_)).randomTest(1000)
  }

  it should "pass an inductive proof" in {
    test(new ToyCpu)(new ToyCpuProtocols(_)).proof(new ToyCpuInvariants(_, _))
  }
}

class ToyCpuInvariants(impl: ToyCpu, spec: ToyCpuModel) extends ProofCollateral(impl, spec) {
  mapping { (impl, spec) =>
    assert(impl.regs === spec.regs)
  }
  invariants { impl =>
    assert(!impl.secondReadCycle)
  }
}


class ToyCpuModel extends UntimedModule {
  val regs = Mem(4, UInt(8.W))
  val add = fun("add").in(new RegArgs) { in =>
    regs.write(in.r0, regs.read(in.r0) + regs.read(in.r1))
  }
  val load = fun("load").in(new LoadArgs).out(UInt(8.W)) { (in, addr) =>
    addr := regs.read(in.r1)
    regs.write(in.r0, in.data)
  }
  val store = fun("store").in(new RegArgs).out(new StoreOut) { (in, out) =>
    out.addr := regs.read(in.r1)
    out.data := regs.read(in.r0)
  }
}
class RegArgs extends Bundle {
  val r0 = UInt(2.W) // dest + arg0
  val r1 = UInt(2.W) // arg1
}
class LoadArgs extends Bundle {
  val r0 = UInt(2.W) // dest
  val r1 = UInt(2.W) // addr
  val data = UInt(8.W)
}
class StoreOut extends Bundle {
  val addr = UInt(8.W)
  val data = UInt(8.W)
}

class ToyCpuProtocols(impl: ToyCpu) extends ProtocolSpec[ToyCpuModel] {
  val spec = new ToyCpuModel

  protocol(spec.add) (impl.io){ (clock, io, in) =>
    io.instruction.bits.poke(0.U(2.W) ## in.r0 ## in.r1 ## 0.U(2.W))
    io.instruction.valid.poke(true.B)
    io.instruction.ready.expect(true.B)
    io.doRead.expect(false.B)
    io.doWrite.expect(false.B)
    clock.step()
  }

  protocol(spec.load) (impl.io){ (clock, io, in, addr) =>
    io.instruction.bits.poke(1.U(2.W) ## in.r0 ## in.r1 ## 0.U(2.W))
    io.instruction.valid.poke(true.B)
    io.instruction.ready.expect(true.B)
    io.memAddr.expect(addr)
    io.doRead.expect(true.B)
    io.doWrite.expect(false.B)
    clock.step()
    // data arrives after one cycle
    io.memDataIn.poke(in.data)
    io.instruction.ready.expect(false.B)
    io.doRead.expect(false.B)
    io.doWrite.expect(false.B)
    clock.step()
  }

  protocol(spec.store) (impl.io){ (clock, io, in, out) =>
    io.instruction.bits.poke(2.U(2.W) ## in.r0 ## in.r1 ## 0.U(2.W))
    io.instruction.valid.poke(true.B)
    io.instruction.ready.expect(true.B)
    io.memAddr.expect(out.addr)
    io.memDataOut.expect(out.data)
    io.doRead.expect(false.B)
    io.doWrite.expect(true.B)
    clock.step()
  }
}


class ToyCpuIO extends Bundle {
  val instruction = Flipped(Decoupled(UInt(8.W)))
  val memAddr = Output(UInt(8.W))
  val memDataIn = Input(UInt(8.W))
  val memDataOut = Output(UInt(8.W))
  val doWrite = Output(Bool())
  val doRead = Output(Bool())
}

class ToyCpu extends Module {
  val io = IO(new ToyCpuIO)

  // decode
  val op = io.instruction.bits(7,6)
  val r0 = io.instruction.bits(5,4)
  val r1 = io.instruction.bits(3,2)
  val rd = r0

  // register file
  val regs = Mem(4, UInt(8.W))
  // ensure that all registers start at zero just like in our model
  annotate(new ChiselAnnotation {
    override def toFirrtl = MemoryScalarInitAnnotation(regs.toAbsoluteTarget, 0)
  })
  val arg0 = regs.read(r0)
  val arg1 = regs.read(r1)
  val res = WireInit(0.U(8.W))
  val doWrite = WireInit(false.B)
  when(doWrite && !(reset.asBool())) { regs.write(r0, res) }

  // memory defaults
  io.memAddr := arg1
  io.doRead := false.B
  io.doWrite := false.B
  io.memDataOut := arg0

  // a read from memory takes two cycles
  val secondReadCycle = RegInit(false.B)
  io.instruction.ready := !secondReadCycle

  when(secondReadCycle) {
    res := io.memDataIn
    doWrite := true.B
    secondReadCycle := false.B
  } .elsewhen(io.instruction.fire()) {
    switch(op) {
      is(0.U) { // ADD
        res := arg0 + arg1
        doWrite := true.B
      }
      is(1.U) { // LOAD
        secondReadCycle := true.B
        io.doRead := true.B
      }
      is(2.U) { // STORE
        io.doWrite := true.B
      }
    }
  }
}
