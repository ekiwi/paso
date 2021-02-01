package benchmarks.fifo.paper

import org.scalatest.flatspec.AnyFlatSpec
import paso._

class PaperFifoProofs extends AnyFlatSpec with PasoTester {
  "Fifo" should "refine its spec" in {
    test(new Fifo(8))(new FifoP(_)).proof(Paso.MCZ3, new FifoI(_, _))
  }

  "Fifo" should "pass bmc" in {
    test(new Fifo(8))(new FifoP(_)).bmc(6)
  }

  "Fifo" should "pass randomTesting" in {
    test(new Fifo(8))(new FifoP(_)).randomTest(60 * 1000)
  }
}