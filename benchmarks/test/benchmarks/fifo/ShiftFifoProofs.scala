package benchmarks.fifo

import org.scalatest.flatspec.AnyFlatSpec
import paso._
import chisel3._

class ShiftFifoProofs extends AnyFlatSpec {

  "ShiftFifo" should "refine its spec" in {
    val depth = 8
    val width = 8
    val fixed = true

    Paso(new ShiftRegisterFifo(depth, width, fixed))(new FifoProtocols(_)).proof(Paso.MCBotr, new ShiftProof(_, _))
  }

  "ShiftFifo" should "not fail bmc" in {
    val depth = 8
    val width = 8
    val fixed = true

    Paso(new ShiftRegisterFifo(depth, width, fixed))(new FifoProtocols(_)).bmc(8)
  }

  "ShiftFifo with bug" should "fail BMC" in {
    val fail = intercept[AssertionError] {
      Paso(new ShiftRegisterFifo(8, 4, false))(new FifoProtocols(_)).bmc(8)
    }
    assert(fail.getMessage.contains("Found a disagreement between implementation and spec"))
  }

  "ShiftFifo" should "not fail 1k cycles of random testing" in {
    val depth = 8
    val width = 8
    val fixed = true

    Paso(new ShiftRegisterFifo(depth, width, fixed))(new FifoProtocols(_)).randomTest(1000)
  }

  "ShiftFifo with bug" should "fail within 1k cycles of random testing" in {
    val depth = 8
    val width = 8
    val fixed = false

    assertThrows[AssertionError] {
      Paso(new ShiftRegisterFifo(depth, width, fixed))(new FifoProtocols(_)).randomTest(1000)
    }
  }
}