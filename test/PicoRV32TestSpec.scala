import org.scalatest._
import chisel3._
import chiseltest._
import chiseltest.experimental.TestOptionBuilder._
import chiseltest.internal.WriteVcdAnnotation
import impl.PicoRV32Mul

class PicoRV32TestSpec extends FlatSpec with ChiselScalatestTester {

  val withVcd = Seq(WriteVcdAnnotation)
  val noVcd = Seq()

  val MUL    = "000" // lower 32bits
  val MULH   = "001" // upper 32bits   signed x signed
  val MULHU  = "011" // upper 32bits unsigned x unsigned
  val MULHSU = "010" // upper 32bits   signed x unsigned

  val mask32 = (BigInt(1) << 32) - 1
  val mask64 = (BigInt(1) << 64) - 1
  val bit31 = BigInt(1) << 31
  def asSigned32(v: BigInt): BigInt = {
    assert((v & mask32) == v)
    val isPositive = (v & bit31) == 0
    if(isPositive) { v } else {
      val abs = ((~v) & mask32) + 1
      -abs
    }
  }
  def fromSigned64(v: BigInt): BigInt = {
    if(v >= 0) { v } else {
      ((~v.abs) & mask64) + 1
    }
  }

  def do_mul(op: String, a: BigInt, b: BigInt): BigInt = {
    assert((a & mask32) == a && (b & mask32) == b)
    val res = op match {
      case MUL => a * b
      case MULH =>
        val product = asSigned32(a) * asSigned32(b)
        fromSigned64(product) >> 32
      case MULHU => (a * b) >> 32
      case MULHSU =>
        val product = asSigned32(a) * b
        fromSigned64(product) >> 32
      case other => throw new RuntimeException(s"unsupported op $other")
    }
    assert(res >= 0)
    res & mask32
  }

  def mulProtocol(dut: PicoRV32Mul, op: String, rs1: BigInt, rs2: BigInt, rd: BigInt): Unit = {
    val instr = "0000001" + "0000000000" + op + "00000" + "0110011"
    assert(instr.length == 32)

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
    dut.io.valid.poke(false.B)
    dut.clock.step()
  }

  "PicoRV32Mul" should "correctly multiply 100 and 7" in {
    test(new PicoRV32Mul(stepsAtOnce = 1, carryChain = 0)).withAnnotations(withVcd) { dut =>
      val (rs1, rs2) = (BigInt(100), BigInt(7))
      val rd = do_mul(MULHU, rs1, rs2)
      mulProtocol(dut, MULHU, rs1, rs2, rd)
    }
  }

  "PicoRV32Mul" should "correctly MUL 100 different numbers" in {
    val random = new scala.util.Random(0)
    test(new PicoRV32Mul(stepsAtOnce = 1, carryChain = 0)).withAnnotations(withVcd) { dut =>
      (0 until 100).foreach{ _ =>
        val (rs1, rs2) = (BigInt(32, random), BigInt(32, random))
        val rd = do_mul(MUL, rs1, rs2)
        mulProtocol(dut, MUL, rs1, rs2, rd)
      }
    }
  }

  "PicoRV32Mul" should "correctly MULH 100 different numbers" in {
    val random = new scala.util.Random(0)
    test(new PicoRV32Mul(stepsAtOnce = 1, carryChain = 0)).withAnnotations(withVcd) { dut =>
      (0 until 100).foreach{ _ =>
        val (rs1, rs2) = (BigInt(32, random), BigInt(32, random))
        val rd = do_mul(MULH, rs1, rs2)
        mulProtocol(dut, MULH, rs1, rs2, rd)
      }
    }
  }

  "PicoRV32Mul" should "correctly MULHU 100 different numbers" in {
    val random = new scala.util.Random(0)
    test(new PicoRV32Mul(stepsAtOnce = 1, carryChain = 0)).withAnnotations(withVcd) { dut =>
      (0 until 100).foreach{ _ =>
        val (rs1, rs2) = (BigInt(32, random), BigInt(32, random))
        val rd = do_mul(MULHU, rs1, rs2)
        mulProtocol(dut, MULHU, rs1, rs2, rd)
      }
    }
  }

  "PicoRV32Mul" should "correctly MULHSU 100 different numbers" in {
    val random = new scala.util.Random(0)
    test(new PicoRV32Mul(stepsAtOnce = 1, carryChain = 0)).withAnnotations(withVcd) { dut =>
      (0 until 100).foreach{ _ =>
        val (rs1, rs2) = (BigInt(32, random), BigInt(32, random))
        val rd = do_mul(MULHSU, rs1, rs2)
        mulProtocol(dut, MULHSU, rs1, rs2, rd)
      }
    }
  }
}
