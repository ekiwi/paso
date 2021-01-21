package benchmarks.fifo

import chisel3._
import chisel3.util._
import paso._


class UntimedQueue[G <: Data](val depth: Int, val dataType: G, val pushPopWhenEmpty: Boolean, val pushPopWhenFull: Boolean) extends UntimedModule {
  require(depth > 0)
  require(isPow2(depth))
  val mem = Mem(depth, dataType)
  val count = RegInit(UInt((log2Ceil(depth) + 1).W), 0.U)
  val read = RegInit(UInt(log2Ceil(depth).W), 0.U)
  val full = count === depth.U
  val empty = count === 0.U

  val push = fun("push").in(dataType).out(new PushOut(chiselTypeOf(count))).when(!full) { (dataIn, out) =>
    mem.write(read + count, dataIn)
    count := count + 1.U
    out.count := count
    out.empty := empty
  }

  val pop = fun("pop").out(new PopOut(dataType, chiselTypeOf(count))).when(!empty) { out =>
    out.data := mem.read(read)
    out.count := count
    out.full := full
    count := count - 1.U
    read := read + 1.U
  }

  val pushPopGuard = (if(pushPopWhenEmpty) true.B else !empty) && (if(pushPopWhenFull) true.B else !full)
  val push_pop = fun("push_pop").in(dataType).out(new PopOut(dataType, chiselTypeOf(count)))
    .when(pushPopGuard) { (in, out) =>
    when(empty) {
      out.data := in
    }.otherwise {
      mem.write(read + count,  in)
      out.data := mem.read(read)
    }
    read := read + 1.U
    out.count := count
    out.full := full
  }

  val idle = fun("idle").out(new IdleOut(chiselTypeOf(count))) { out =>
    out.count := count
    out.empty := empty
    out.full := full
  }
}

class PopOut[G <: Data, C <: Data](private val dataType: G, private val countType: C) extends Bundle {
  val data = dataType
  val count = countType
  val full = Bool()
}

class PushOut[C <: Data](private val countType: C) extends Bundle {
  val count = countType
  val empty = Bool()
}

class IdleOut[C <: Data](private val countType: C) extends Bundle {
  val count = countType
  val empty = Bool()
  val full = Bool()
}

class ChiselQueueProtocol[T <: UInt](impl: Queue[T]) extends ProtocolSpec[UntimedQueue[T]] {
  val spec = new UntimedQueue[T](impl.entries, impl.gen, pushPopWhenEmpty = impl.flow, pushPopWhenFull = impl.pipe)

  override val stickyInputs = false

  // alternative which might be nicer as it would allow us to keep all of spec constant
  protocol(spec.push)(impl.io) { (clock, dut, in, out) =>
    // ideally we would be able to separately describe the three interfaces...

    // enqueue
    dut.enq.valid.set(true.B)
    dut.enq.bits.set(in)
    dut.enq.ready.expect(true.B)

    // dequeue
    dut.deq.ready.set(false.B) // do not pop
    // we do not care about the data
    if(impl.flow) {
      dut.deq.valid.expect(true.B)
    } else {
      dut.deq.valid.expect(!out.empty)
    }

    // count
    dut.count.expect(out.count)

    clock.step()
  }

  protocol(spec.pop)(impl.io) { (clock, dut, out) =>
    // ideally we would be able to separately describe the three interfaces...

    // enqueue
    dut.enq.valid.set(false.B)
    dut.enq.bits.set(DontCare)
    if(impl.pipe) {
      dut.enq.ready.expect(true.B)
    } else {
      dut.enq.ready.expect(!out.full)
    }

    // dequeue
    dut.deq.ready.set(true.B)
    dut.deq.bits.expect(out.data)
    dut.deq.valid.expect(true.B)

    // count
    dut.count.expect(out.count)

    clock.step()
  }

  protocol(spec.push_pop)(impl.io) { (clock, dut, in, out) =>
    // ideally we would be able to separately describe the three interfaces...

    // enqueue
    dut.enq.valid.set(true.B)
    dut.enq.bits.set(in)
    dut.enq.ready.expect(true.B)

    // dequeue
    dut.deq.ready.set(true.B)
    dut.deq.bits.expect(out.data)
    dut.deq.valid.expect(true.B)

    // count
    dut.count.expect(out.count)

    clock.step()
  }

  protocol(spec.idle)(impl.io) { (clock, dut, out) =>
    // enqueue
    dut.enq.valid.set(false.B)
    dut.enq.bits.set(DontCare)
    dut.enq.ready.expect(!out.full)

    // dequeue
    dut.deq.ready.set(false.B)
    dut.deq.valid.expect(!out.empty)

    // count
    dut.count.expect(out.count)

    clock.step()
  }
}