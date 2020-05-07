package aes

import chisel3._
import chiseltest._
import chiseltest.experimental.TestOptionBuilder._
import chiseltest.internal.{VerilatorBackendAnnotation, WriteVcdAnnotation}
import org.scalatest._

class TinyAESTestSpec extends FlatSpec with ChiselScalatestTester {
  val withVcd = Seq(WriteVcdAnnotation)
  val noVcd = Seq()
  val withVerilator = Seq(VerilatorBackendAnnotation)

  def roundProtocol(clock: Clock, dut: RoundIO, key: UInt, state: UInt, nextState: UInt): Unit = {
    dut.state.poke(state)
    clock.step()
    dut.state.poke(0.U)
    dut.key.poke(key)
    clock.step()
    dut.key.poke(0.U)
    dut.stateNext.expect(nextState)
  }

  def optimisticRoundProtocol(clock: Clock, dut: RoundIO, key: UInt, state: UInt, nextState: UInt): Unit = {
    dut.state.poke(state)
    dut.key.poke(key)
    clock.step()
    clock.step()
    dut.stateNext.expect(nextState)
  }

  "OneRound" should "do its thing" in {
    test(new OneRound).withAnnotations(withVcd) { dut =>
      val key = 0.U
      val state = "d259246292300786127265179315961154317583".U
      val nextState = 0.U
      optimisticRoundProtocol(dut.clock, dut.io, key, state, nextState)
    }
  }

}
