package aes
/*
import chisel3._
import chiseltest._
import chiseltest.experimental.TestOptionBuilder._
import chiseltest.internal.{VerilatorBackendAnnotation, WriteVcdAnnotation}
import org.scalatest.flatspec.AnyFlatSpec

class TinyAESTest extends AnyFlatSpec with ChiselScalatestTester {
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

  def aesProtocol(clock: Clock, dut: TinyAES128IO, key: UInt, state: UInt, out: UInt): Unit = {
    // apply state and key for one cycle
    dut.state.poke(state)
    dut.key.poke(key)
    clock.step()
    dut.state.poke(0.U)
    dut.key.poke(0.U)

    // wait 20 cycles (for a total of 21 = 10 rounds with delay 2 + 1 initial round)
    (0 until 20).foreach(_ => clock.step())
    dut.out.expect(out)
  }

  "OneRound" should "do its thing" in {
    test(new OneRound).withAnnotations(withVcd) { dut =>
      val key = 0.U
      val state = "d259246292300786127265179315961154317583".U
      val nextState = 0.U
      optimisticRoundProtocol(dut.clock, dut.io, key, state, nextState)
    }
  }

  // with example values from the TinyAES test bench
  "TinyAES128" should "compute a block correctly" in {
    test(new TinyAES128).withAnnotations(withVcd) { dut =>
      val state = "h3243f6a8_885a308d_313198a2_e0370734".U
      val key = "h2b7e1516_28aed2a6_abf71588_09cf4f3c".U
      val result = "h3925841d02dc09fbdc118597196a0b32".U
      aesProtocol(dut.clock, dut.io, key, state, result)
    }
  }

  "TinyAES128" should "compute a different block correctly" in {
    test(new TinyAES128).withAnnotations(withVcd) { dut =>
      val state = 0.U(128.W)
      val key = 0.U(128.W)
      val result = "h66_e9_4b_d4_ef_8a_2c_3b_88_4c_fa_59_ca_34_2b_2e".U
      aesProtocol(dut.clock, dut.io, key, state, result)
    }
  }

  // https://kavaliro.com/wp-content/uploads/2014/03/AES.pdf
  "TinyAES128" should "compute another block correctly" in {
    test(new TinyAES128).withAnnotations(withVcd) { dut =>
      val state  = "h54776F204F6E65204E696E652054776F".U
      val key    = "h5468617473206D79204B756E67204675".U
      val result = "h29C3505F571420F6402299B31A02D73A".U
      aesProtocol(dut.clock, dut.io, key, state, result)
    }
  }




}
*/
