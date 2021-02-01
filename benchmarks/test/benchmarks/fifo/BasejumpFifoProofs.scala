package benchmarks.fifo

import org.scalatest.flatspec.AnyFlatSpec
import paso._
import chisel3._

class BasejumpFifoProofs extends AnyFlatSpec with PasoTester {
  "BasejumpFifo" should "refine its spec" ignore {
    test(new BasejumpFifo(8, 8))(new BasejumpFifoProtocols(_)).proof()
  }

}