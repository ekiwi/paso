package benchmarks.fifo.paper

import org.scalatest.flatspec.AnyFlatSpec
import paso._

class PaperFifoProofs extends AnyFlatSpec {
  "Fifo" should "refine its spec" in {
    Paso(new Fifo(8))(new FifoP(_)).proof(Paso.MCZ3, new FifoI(_, _))
  }

  "Fifo" should "pass bmc" in {
    Paso(new Fifo(8))(new FifoP(_)).bmc(6)
  }
}