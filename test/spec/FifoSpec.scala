package spec

import chisel3._
import chisel3.util._
import impl.{CircularPointerFifo, IsFifo, ShiftRegisterFifo}
import org.scalatest._
import paso._
import paso.chisel.Elaboration
import paso.verification.VerificationProblem



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

class FifoProtocols[F <: IsFifo](impl: F, spec: UntimedFifo[UInt]) extends Binding(impl, spec) {
  // TODO: instantiate spec based on impl parametrization
  require(impl.width == spec.dataType.getWidth)
  require(impl.depth == spec.depth)

  // alternative which might be nicer as it would allow us to keep all of spec constant
  protocol(spec.push)(impl.io) { (clock, dut, in) =>
    dut.pop.poke(false.B)
    dut.push.poke(true.B)
    dut.data_in.poke(in)
    dut.full.expect(false.B)
    clock.step()
  }

  protocol(spec.pop)(impl.io) { (clock, dut, out) =>
    dut.pop.poke(true.B)
    dut.push.poke(false.B)
    dut.data_out.expect(out)
    dut.empty.expect(false.B)
    clock.step()
  }

  protocol(spec.push_pop)(impl.io) { (clock, dut, in, out) =>
    dut.pop.poke(true.B)
    dut.push.poke(true.B)
    dut.data_in.poke(in)
    dut.data_out.expect(out)
    dut.empty.expect(false.B)
    clock.step()
  }

  protocol(spec.idle)(impl.io) { (clock, dut) =>
    dut.pop.poke(false.B)
    dut.push.poke(false.B)
    clock.step()
  }
}

class CircularBinding(impl: CircularPointerFifo, spec: UntimedFifo[UInt]) extends FifoProtocols(impl, spec) {
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

class ShiftBinding(impl: ShiftRegisterFifo, spec: UntimedFifo[UInt]) extends FifoProtocols(impl, spec) {
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
  val depth = 8
  val width = 8
  val fixed = true

  val p = Elaboration[CircularPointerFifo, UntimedFifo[UInt]](
    new CircularPointerFifo(depth = depth, width = width, fixed = fixed),
    new UntimedFifo(depth = depth, dataType = UInt(width.W)),
    (impl, spec) => new CircularBinding(impl, spec)
  )

  VerificationProblem.verify(p)
}

class ShiftFifoSpec extends FlatSpec {
  val depth = 8
  val width = 8
  val fixed = true

  val p = Elaboration[ShiftRegisterFifo, UntimedFifo[UInt]](
    new ShiftRegisterFifo(depth = depth, width = width, fixed = fixed),
    new UntimedFifo(depth = depth, dataType = UInt(width.W)),
    (impl, spec) => new ShiftBinding(impl, spec)
  )

  VerificationProblem.verify(p)
}
