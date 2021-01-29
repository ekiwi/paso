package benchmarks.fifo

import org.scalatest.flatspec.AnyFlatSpec
import paso._
import chisel3._
import chisel3.util._


class ChiselQueueProofs extends AnyFlatSpec {

  def makeTest(c: QueueConfig): Unit = {
    val k = (c.depth * 2) + 2
    s"Chisel Queue(UInt(${c.width}.W), depth=${c.depth}, flow=${c.flow}, pipe=${c.pipe})" should s"pass BMC(k=$k)" in {
      Paso(new Queue(UInt(c.width.W), c.depth, flow = c.flow, pipe = c.pipe))(new ChiselQueueProtocol(_)).bmc(k)
    }

    val j = k * 1000
    s"Chisel Queue(UInt(${c.width}.W), depth=${c.depth}, flow=${c.flow}, pipe=${c.pipe})" should s"pass random testing (k=$j)" in {
      Paso(new Queue(UInt(c.width.W), c.depth, flow = c.flow, pipe = c.pipe))(new ChiselQueueProtocol(_)).randomTest(j)
    }
  }

  val defaultWidth = 8
  val depths = List(1,2,3,4)
  val configs =
    List(false, true).flatMap { pipe =>
      List(false, true).flatMap { flow =>
        depths.map { depth =>
          QueueConfig(width = defaultWidth, depth=depth, flow=flow, pipe=pipe)
        }
      }
    }
  configs.foreach(makeTest)
}

case class QueueConfig(width: Int, depth: Int, flow: Boolean, pipe: Boolean)