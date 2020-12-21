package benchmarks.fifo

import org.scalatest.flatspec.AnyFlatSpec
import paso._
import chisel3._

class BasejumpFifoProofs extends AnyFlatSpec {
  "BasejumpFifo" should "refine its spec" ignore {
    Paso(new BasejumpFifo(8, 8))(new BasejumpFifoProtocols(_)).proof()
  }

}