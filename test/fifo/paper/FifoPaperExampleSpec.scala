package fifo.paper

import chisel3._
import chisel3.util._
import fifo.BasejumpFifoIO
import org.scalatest._
import paso._

class FifoIO(val dataWidth: Int) extends Bundle {
  val dataIn = Input(UInt(dataWidth.W))
  val valid = Input(Bool())
  val pushDontPop = Input(Bool())
  val full = Output(Bool())
  val empty = Output(Bool())
  val dataOut = Output(UInt(dataWidth.W))
}

// based on https://github.com/bespoke-silicon-group/basejump_stl/blob/master/bsg_dataflow/bsg_fifo_1rw_large.v
class Fifo(val depth: Int) extends Module {
  require(isPow2(depth))
  val dataWidth = 32
  val io = IO(new BasejumpFifoIO(dataWidth))

  val pointerWidth = log2Ceil(depth)

  val memWrite = io.pushDontPop && io.valid
  val memRead = !io.pushDontPop && io.valid
  val lastRd = RegInit(true.B)
  when(io.valid) { lastRd := memRead }

  // we simplified things quite a bit by requiring depth to be a power of two
  val rdPtr = RegInit(0.U(pointerWidth.W))
  when(memRead) { rdPtr := rdPtr + 1.U }
  val wrPtr = RegInit(0.U(pointerWidth.W))
  when(memWrite) { wrPtr := wrPtr + 1.U }

  val fifoEmpty = (rdPtr === wrPtr) && lastRd
  val fifoFull = (rdPtr === wrPtr) && !lastRd
  io.empty := fifoEmpty
  io.full := fifoFull

  val mem = SyncReadMem(depth, UInt(dataWidth.W))
  val memAddr = Mux(memWrite, wrPtr, rdPtr)
  val memPort = mem(memAddr)
  io.dataOut := DontCare
  when(memWrite) { memPort := io.dataIn }
    .elsewhen(memRead) { io.dataOut := memPort }

}


class FifoT(val depth: Int) extends UntimedModule {
  val mem = Mem(depth, UInt(32.W))
  val count = RegInit(UInt((log2Ceil(depth) + 1).W), 0.U)
  val read = RegInit(UInt(log2Ceil(depth).W), 0.U)
  val full = count === depth.U
  val empty = count === 0.U

  val push = fun("push").in(UInt(32.W)).when(!full) { in =>
    mem(read + count) := in
    count := count + 1.U
  }
  val pop = fun("pop").out(UInt(32.W)).when(!empty) { out =>
    out := mem(read)
    count := count - 1.U
    read := read + 1.U
  }
  val idle = fun("idle"){}
}

class FifoP(impl: Fifo) extends ProtocolSpec[FifoT] {
  val spec = new FifoT(impl.depth)

  protocol(spec.push)(impl.io) { (clock, dut, in) =>
    dut.pushDontPop.set(true.B)
    dut.valid.set(true.B)
    dut.dataIn.set(in)
    dut.full.expect(false.B)
    clock.step()
  }

  protocol(spec.pop)(impl.io) { (clock, dut, out) =>
    dut.pushDontPop.set(false.B)
    dut.valid.set(true.B)
    dut.empty.expect(false.B)
    clock.stepAndFork()
    dut.pushDontPop.set(DontCare)
    dut.valid.set(DontCare)
    dut.dataIn.set(DontCare)
    dut.dataOut.expect(out)
    clock.step()
  }

  protocol(spec.idle)(impl.io) { (clock, dut) =>
    dut.valid.set(false.B)
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

class FifoPaperExampleSpec extends FlatSpec {
  "Fifo" should "refine its spec" in {
    Paso(new Fifo(8))(new FifoP(_)).proof(new FifoI(_, _))
  }
}
