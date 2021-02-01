package benchmarks.picorv32

import org.scalatest.flatspec.AnyFlatSpec
import paso._

class PicoRV32Proofs extends AnyFlatSpec with PasoTester {
  "PicoRV32Mul" should "pass some cycles of random testing" in {
    test(new PicoRV32Mul())(new MulProtocols(_)).randomTest(k=10000)
  }

  "PicoRV32Mul" should "pass some cycles of BMC" in {
    // NOTE: the kMax is not deep enough to actually verify correct multiplication ...
    test(new PicoRV32Mul())(new MulProtocols(_)).bmc(32)
  }

  // this will timeout because multiplication is hard...
  "PicoRV32Mul" should "refine its spec" ignore {
    test(new PicoRV32Mul())(new MulProtocols(_)).proof(new ProofCollateral(_, _){
      invariants { dut =>
        assert(dut.mulWaiting)
        assert(!dut.mulFinishDelay)
        assert(!dut.mulFinish)
        assert(!dut.doWait)
      }
    })
  }
}