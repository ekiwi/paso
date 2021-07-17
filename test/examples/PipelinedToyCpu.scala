package examples

import chisel3._
import chisel3.experimental.{ChiselAnnotation, annotate}
import chisel3.util._
import firrtl.annotations.MemoryScalarInitAnnotation
import org.scalatest.flatspec.AnyFlatSpec
import paso._

class PipelinedToyCpuSpec extends AnyFlatSpec with PasoTester {
  behavior of "PipelinedToyCpu"

  it should "pass some cycles of BMC" ignore {
    test(new PipelinedToyCpu)(new PipelinedToyCpuProtocols(_)).bmc(4)
  }

  it should "pass some cycles of random testing" ignore {
    test(new PipelinedToyCpu)(new PipelinedToyCpuProtocols(_)).randomTest(1000, recordWaveform = true, seed = Some(1))
  }
}

class PipelinedToyCpuProtocols(impl: PipelinedToyCpu) extends ProtocolSpec[ToyCpuModel] {
  val spec = new ToyCpuModel(noLoad = true)

  override val stickyInputs: Boolean = false

  protocol(spec.add) (impl.io){ (clock, io, in) =>
    // instruction fetch
    io.instruction.bits.poke(0.U(2.W) ## in.r0 ## in.r1 ## 0.U(2.W))
    io.instruction.valid.poke(true.B)
    io.instruction.ready.expect(true.B)
    clock.stepAndFork()
    // execution
    io.doRead.expect(false.B)
    io.doWrite.expect(false.B)
    clock.step()
  }

  /*
  protocol(spec.load) (impl.io){ (clock, io, in, addr) =>
    // instruction fetch
    io.instruction.bits.poke(1.U(2.W) ## in.r0 ## in.r1 ## 0.U(2.W))
    io.instruction.valid.poke(true.B)
    io.instruction.ready.expect(true.B)
    // execution
    clock.step()
    io.memAddr.expect(addr)
    io.doRead.expect(true.B)
    io.doWrite.expect(false.B)
    io.instruction.ready.expect(false.B)
    clock.stepAndFork()
    // data arrives after one cycle
    io.memDataIn.poke(in.data)
    io.doRead.expect(false.B)
    io.doWrite.expect(false.B)
    clock.step()
  }
   */

  protocol(spec.store) (impl.io){ (clock, io, in, out) =>
    // instruction fetch
    io.instruction.bits.poke(2.U(2.W) ## in.r0 ## in.r1 ## 0.U(2.W))
    io.instruction.valid.poke(true.B)
    io.instruction.ready.expect(true.B)
    clock.stepAndFork()
    // execution
    io.memAddr.expect(out.addr)
    io.memDataOut.expect(out.data)
    io.doRead.expect(false.B)
    io.doWrite.expect(true.B)
    clock.step()
  }
}


class PipelinedToyCpu(enableBug: Int = 0) extends Module {
  val io = IO(new ToyCpuIO)

  // fetch
  val instr = RegNext(io.instruction.bits)
  val instrValid = RegNext(io.instruction.fire(), init = false.B)

  // decode
  val op = instr(7,6)
  val r0 = instr(5,4)
  val r1 = instr(3,2)
  val rd = r0

  // debug
  dontTouch(op)
  dontTouch(r0)
  dontTouch(r1)

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
  io.instruction.ready := secondReadCycle || op =/= 1.U

  when(secondReadCycle) {
    res := io.memDataIn
    doWrite := true.B
    if(enableBug != 1) { // bug #1: we forgot to reset the state
      secondReadCycle := false.B
    }
  } .elsewhen(instrValid) {
    switch(op) {
      is(0.U) { // ADD
        res := arg0 + arg1
        if(enableBug != 2) { // bug #2 we forgot to write the result of an ALU operation to the register file
          doWrite := true.B
        }
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
