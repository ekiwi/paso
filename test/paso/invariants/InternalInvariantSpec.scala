// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.invariants

import org.scalatest.flatspec.AnyFlatSpec
import paso._
import chisel3._

// This counter has no IO besides clock and reset.
// This models a CPU that can only do reg2reg instructions.
// While both examples are not directly useful, we want to be able to verify
// a design while it is being built, thus we need to support circuits like this.
class InternalCounter extends Module {
  val count = RegInit(0.U(8.W))
  count := count + 1.U
}

class UntimedCounter extends UntimedModule {
  // we are using a mem here because keeping mems around can be harder than keeping registers
  val count = Mem(1, UInt(8.W))
  val inc = fun("inc") {
    count.write(0.U, count.read(0.U) + 1.U)
  }
}

class InternalCounterProtocol(impl: InternalCounter) extends ProtocolSpec[UntimedCounter] {
  val spec = new UntimedCounter
  protocol(spec.inc)(impl.reset) { (clock, dut) =>
    clock.step()
  }
}

class InternalCounterProof(impl: InternalCounter, spec: UntimedCounter) extends ProofCollateral(impl, spec) {
  mapping { (impl, spec) =>
    assert(impl.count === spec.count.read(0.U))
  }
}

class InternalInvariantSpec extends AnyFlatSpec with PasoTester {
  behavior of "Paso invariants with internal behavior"

  // small sanity check
  it should "work for bmc ...." in { test(new InternalCounter)(new InternalCounterProtocol(_)).bmc(5) }
  it should "work for random ...." in { test(new InternalCounter)(new InternalCounterProtocol(_)).randomTest(5) }

  // the important part here is that the internal registers that the invariants refer to do not
  // get optimized away!
  it should "pass a proof" in {
    val dbg = DebugOptions(printInductionSys = false)
    test(new InternalCounter)(new InternalCounterProtocol(_)).proof(Paso.Default, dbg, new InternalCounterProof(_, _))
  }

}
