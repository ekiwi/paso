package benchmarks.fifo

import org.scalatest.flatspec.AnyFlatSpec
import paso._
import chisel3._

class CircularPointerFifoProofs extends AnyFlatSpec {

  "CircularPointerFifo" should "refine its spec" in {
    val depth = 8
    val width = 8
    val fixed = true

    Paso(new CircularPointerFifo(depth, width, 0, fixed))(new FifoProtocols(_)).proof(Paso.MCZ3, new CircularProof(_, _))
  }

  "CircularPointerFifo with readDelay=1" should "refine its spec" in {
    val depth = 8
    val width = 8
    val fixed = true

    Paso(new CircularPointerFifo(depth, width, 1, fixed))(new FifoProtocols(_)).proof(Paso.MCBotr, new CircularProof(_, _))
  }
}