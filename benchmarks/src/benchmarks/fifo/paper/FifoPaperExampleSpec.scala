package benchmarks.fifo.paper

import chisel3._
import chisel3.util._
import paso._

// based on https://github.com/bespoke-silicon-group/basejump_stl/blob/master/bsg_dataflow/bsg_fifo_1rw_large.v
class Fifo(val depth: Int) extends Module {
  require(isPow2(depth))
  val io = IO(new Bundle {
    val dataIn = Input(UInt(32.W))
    val valid = Input(Bool())
    val pushDontPop = Input(Bool())
    val dataOut = Output(UInt(32.W))
  })

  val memWrite = io.pushDontPop && io.valid
  val memRead = !io.pushDontPop && io.valid
  val lastRd = RegInit(true.B)
  when(io.valid) { lastRd := memRead }

  val wrPtr = RegInit(0.U(3.W))
  when(memWrite) { wrPtr := wrPtr + 1.U }
  val rdPtr = RegInit(0.U(3.W))
  val empty = (rdPtr === wrPtr) && lastRd
  when(memRead && !empty) { rdPtr := rdPtr + 1.U }

  val mem = SyncReadMem(depth, UInt(32.W))
  val memAddr = Mux(memWrite, wrPtr, rdPtr)
  io.dataOut := DontCare

  if(false) {
    val memPort = mem(memAddr)
    when(memWrite) { memPort := io.dataIn }
      // the following is broken since the data will only be available with a one cycle delay...
   .elsewhen(memRead) { io.dataOut := memPort }
  } else {
    when(memWrite) { mem.write(memAddr, io.dataIn) }
    io.dataOut := mem.read(memAddr, !memWrite)
  }
}

class FifoT(val depth: Int) extends UntimedModule {
  val mem = Mem(depth, UInt(32.W))
  val count = RegInit(0.U((log2Ceil(depth) + 1).W))
  val read = RegInit(0.U(log2Ceil(depth).W))
  val full = count === depth.U
  val empty = count === 0.U

  val push = fun("push").in(UInt(32.W)).when(!full)
  { in =>
    mem.write(read + count, in)
    count := count + 1.U
  }
  val pop = fun("pop").out(Valid(UInt(32.W))) { out =>
    when(empty) {
      out.valid := false.B
    } .otherwise {
      out.bits := mem.read(read)
      out.valid := true.B
      count := count - 1.U
      read := read + 1.U
    }
  }
  val idle = fun("idle"){}
}

class FifoP(impl: Fifo) extends ProtocolSpec[FifoT] {
  val spec = new FifoT(impl.depth)
  override val stickyInputs: Boolean = false

  protocol(spec.push)(impl.io) { (clock, duv, in) =>
    duv.pushDontPop.set(true.B)
    duv.valid.set(true.B)
    duv.dataIn.set(in)
    clock.step()
  }

  protocol(spec.pop)(impl.io) { (clock, duv, out) =>
    duv.pushDontPop.set(false.B)
    duv.valid.set(true.B)
    clock.stepAndFork()
    when(out.valid) {
      duv.dataOut.expect(out.bits)
    }
    clock.step()
  }

  protocol(spec.idle)(impl.io) { (clock, duv) =>
    duv.valid.set(false.B)
    clock.step()
  }
}


class FifoI(impl: Fifo, spec: FifoT) extends ProofCollateral(impl, spec) {
  mapping { (impl, spec) =>
    when(impl.rdPtr === impl.wrPtr) {
      assert(spec.count === Mux(impl.lastRd, 0.U, impl.depth.U))
    } .elsewhen(impl.wrPtr > impl.rdPtr) {
      assert(spec.count === impl.wrPtr - impl.rdPtr)
    } .otherwise {
      assert(spec.count === impl.depth.U - (impl.rdPtr - impl.wrPtr))
    }
    assert(spec.read === impl.rdPtr)
    forall(0 until impl.depth) { ii =>
      when(spec.count > ii) {
        assert(impl.mem(ii + spec.read) === spec.mem(ii + spec.read))
      }
    }
  }
}
