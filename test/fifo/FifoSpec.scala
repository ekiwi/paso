package fifo

import chisel3._
import chisel3.util._
import org.scalatest._
import paso._

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class UntimedFifo[G <: Data](val depth: Int, val dataType: G) extends UntimedModule {
  require(depth > 0)
  require(isPow2(depth))
  val mem = Mem(depth, dataType)
  val count = RegInit(UInt((log2Ceil(depth) + 1).W), 0.U)
  val read = RegInit(UInt(log2Ceil(depth).W), 0.U)
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

  val idle = fun("idle")() // TODO: closing brackets are unfortunately required for method to be registered for now :(
}

class FifoProtocols[F <: IsFifo](impl: F) extends ProtocolSpec[UntimedFifo[UInt]] {
  val spec = new UntimedFifo[UInt](impl.depth, UInt(impl.width.W))
  val readDelay = impl.readDelay

  // alternative which might be nicer as it would allow us to keep all of spec constant
  protocol(spec.push)(impl.io) { (clock, dut, in) =>
    dut.pop.set(false.B)
    dut.push.set(true.B)
    dut.data_in.set(in)
    dut.full.expect(false.B)
    clock.step()
  }

  protocol(spec.pop)(impl.io) { (clock, dut, out) =>
    dut.pop.set(true.B)
    dut.push.set(false.B)
    dut.empty.expect(false.B)
    if(readDelay == 0) {
      dut.data_out.expect(out)
      clock.step()
    } else {
      (0 until readDelay).foreach(_ => clock.step())
      dut.data_out.expect(out)
    }
  }

  protocol(spec.push_pop)(impl.io) { (clock, dut, in, out) =>
    dut.pop.set(true.B)
    dut.push.set(true.B)
    dut.data_in.set(in)
    dut.empty.expect(false.B)
    if(readDelay == 0) {
      dut.data_out.expect(out)
      clock.step()
    } else {
      (0 until readDelay).foreach(_ => clock.step())
      dut.data_out.expect(out)
    }  }

  protocol(spec.idle)(impl.io) { (clock, dut) =>
    dut.pop.set(false.B)
    dut.push.set(false.B)
    clock.step()
  }
}

class CircularProof(impl: CircularPointerFifo, spec: UntimedFifo[UInt]) extends ProofCollateral(impl, spec) {
  mapping { (impl, spec) =>
    assert(spec.count === impl.cnt)
    assert(spec.read === impl.rdPtr)
    forall(0 until impl.depth) { ii =>
      when(spec.count > ii) {
        assert(impl.entries(ii + spec.read) === spec.mem(ii + spec.read))
      }
    }
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

class ShiftProof(impl: ShiftRegisterFifo, spec: UntimedFifo[UInt]) extends ProofCollateral(impl, spec) {
  mapping { (dut, spec) =>
    assert(dut.count === spec.count)
    (0 until dut.depth).foreach { ii =>
      when(dut.count > ii.U) {
        assert(dut.entries(ii) === spec.mem(spec.read + ii.U))
      }
    }
  }

  invariances { dut => assert(dut.count <= dut.depth.U) }
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class FifoSpec extends FlatSpec {

  "CircularPointerFifo" should "refine its spec" in {
    val depth = 8
    val width = 8
    val fixed = true

    Paso(new CircularPointerFifo(depth, width, fixed))(new FifoProtocols(_)).proof(new CircularProof(_, _))
  }

  "ShiftFifo" should "refine its spec" in {
    val depth = 8
    val width = 8
    val fixed = true

    Paso(new ShiftRegisterFifo(depth, width, fixed))(new FifoProtocols(_)).proof(new ShiftProof(_, _))
  }
}