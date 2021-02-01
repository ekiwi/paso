package benchmarks.fifo

import org.scalatest.flatspec.AnyFlatSpec
import paso._
import chisel3._

class CircularPointerFifoProofs extends AnyFlatSpec with PasoTester {

  "CircularPointerFifo" should "pass BMC" in {
    val depth = 4
    val width = 8
    val fixed = true

    test(new CircularPointerFifo(depth, width, 0, fixed))(new FifoProtocols(_)).bmc((depth * 2) + 2)
  }

  "CircularPointerFifo" should "pass some cycles of random tests" in {
    val depth = 8
    val width = 8
    val fixed = true

    test(new CircularPointerFifo(depth, width, 0, fixed))(new FifoProtocols(_)).randomTest(1000)
  }

  "CircularPointerFifo" should "refine its spec" in {
    val depth = 8
    val width = 8
    val fixed = true

    test(new CircularPointerFifo(depth, width, 0, fixed))(new FifoProtocols(_)).proof(Paso.MCZ3, new CircularProof(_, _))
  }

  "CircularPointerFifo with readDelay=1" should "pass BMC" in {
    val depth = 4
    val width = 8
    val fixed = true

    test(new CircularPointerFifo(depth, width, 1, fixed))(new FifoProtocols(_)).bmc((depth * 2) + 2)
  }

  "CircularPointerFifo with readDelay=1" should "pass some cycles of random tests" in {
    val depth = 8
    val width = 8
    val fixed = true

    test(new CircularPointerFifo(depth, width, 1, fixed))(new FifoProtocols(_)).randomTest(1000)
  }

  "CircularPointerFifo with readDelay=0 and bug" should "fail BMC" ignore {
    val depth = 4
    val width = 8
    val fixed = false // TODO: setting fixed to false still results ina working FIFO ...

    assertThrows[AssertionError] {
      test(new CircularPointerFifo(depth, width, 0, fixed))(new FifoProtocols(_)).bmc((depth * 2) + 2)
    }
  }

  "CircularPointerFifo with readDelay=1 and bug" should "fail random tests" ignore {
    val depth = 8
    val width = 8
    val fixed = false // TODO: setting fixed to false still results ina working FIFO ...

    assertThrows[AssertionError] {
      (0 until 10).foreach { seed =>
        test(new CircularPointerFifo(depth, width, 1, fixed))(new FifoProtocols(_)).randomTest(10000, seed = Some(seed))
      }
    }
  }

  "CircularPointerFifo with readDelay=1" should "refine its spec" in {
    val depth = 8
    val width = 8
    val fixed = true

    test(new CircularPointerFifo(depth, width, 1, fixed))(new FifoProtocols(_)).proof(Paso.MCBotr, new CircularProof(_, _))
  }
}