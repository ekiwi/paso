package benchmarks.picorv32

import org.scalatest.flatspec.AnyFlatSpec
import paso._

class PicoRV32Proofs extends AnyFlatSpec {
  "PicoRV32Mul" should "refine its spec" in {
    Paso(new PicoRV32Mul())(new MulProtocols(_)).proof(new ProofCollateral(_, _){
      invariants { dut =>
        assert(dut.mulWaiting)
        assert(!dut.mulFinishDelay)
        assert(!dut.mulFinish)
        assert(!dut.doWait)
      }
    })
  }
}