import org.scalatest._
import chisel3._
import chiseltest._
import chiseltest.experimental.TestOptionBuilder._
import chiseltest.internal.WriteVcdAnnotation
import impl.PicoRV32Mul

class PicoRV32TestSpec extends FlatSpec with ChiselScalatestTester {

  val withVcd = Seq(WriteVcdAnnotation)
  val noVcd = Seq()

  "PicoRV32Mul" should "multiply unsigned numbers" in {
    test(new PicoRV32Mul(stepsAtOnce = 1, carryChain = 0)).withAnnotations(withVcd) { dut =>
      val instr = "0000001" + "0000000000" + "000" + "00000" + "0110011"
      assert(instr.length == 32)
      val rs1 = BigInt(100)
      val rs2 = BigInt(7)
      val rd = (rs1 * rs2) & ((BigInt(1) << 32) - 1)

      dut.io.valid.poke(true.B)
      dut.io.insn.poke(("b" + instr).U)
      dut.io.rs1.poke(rs1.U)
      dut.io.rs2.poke(rs2.U)
      dut.io.wr.expect(false.B)
      dut.io.ready.expect(false.B)
      dut.clock.step()
      while(!dut.io.ready.peek().litToBoolean) {
        dut.clock.step()
      }
      dut.io.rd.expect(rd.U)
      dut.io.wr.expect(true.B)
    }
  }
}
