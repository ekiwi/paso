package test

import chisel3._
import chiseltest._
import chiseltest.experimental.TestOptionBuilder._
import chiseltest.internal.{VerilatorBackendAnnotation, WriteVcdAnnotation}
import impl.{OriginalPicoRV32Mul, PCPI, PCPIModule, PicoRV32Mul}
import org.scalatest._

class PicoRV32TestSpec extends FlatSpec with ChiselScalatestTester {

  val withVcd = Seq(WriteVcdAnnotation)
  val noVcd = Seq()
  val withVerilator = Seq(VerilatorBackendAnnotation)

  val MUL    = "000" // lower 32bits
  val MULH   = "001" // upper 32bits   signed x signed
  val MULHU  = "011" // upper 32bits unsigned x unsigned
  val MULHSU = "010" // upper 32bits   signed x unsigned
  val allOps = Seq(MUL, MULH, MULHU, MULHSU)

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

  def mulProtocol(io: PCPI, clock: Clock, op: String, rs1: UInt, rs2: UInt, rd: UInt): Unit = {
    val instr = ("b" + "0000001" + "0000000000" + op + "00000" + "0110011").U
    // TODO: we need support for operations on chisel constants
    // val instr: UInt = "b0000001".U ## "b0000000000".U ## op ## "b00000".U ## "b0110011".U
    //assert(instr.getWidth == 32)

    io.valid.poke(true.B)
    io.insn.poke(instr)
    io.rs1.poke(rs1)
    io.rs2.poke(rs2)
    io.wr.expect(false.B)
    io.ready.expect(false.B)
    clock.step()
    while(!io.ready.peek().litToBoolean) {
      clock.step()
    }
    io.rd.expect(rd)
    io.wr.expect(true.B)
    io.valid.poke(false.B)
    clock.step()
  }

  "PicoRV32Mul(stepsAtOnce = 1, carryChain = 0)" should "correctly multiply 100 and 7" in {
    test(new PicoRV32Mul(stepsAtOnce = 1, carryChain = 0)).withAnnotations(withVcd) { dut =>
      val (rs1, rs2) = (BigInt(100), BigInt(7))
      val rd = do_mul(MULHU, rs1, rs2)
      mulProtocol(dut.io, dut.clock, MULHU, rs1.U, rs2.U, rd.U)
    }
  }

  case class TestConfig(stepsAtOnce: Int, carryChain: Int, op: String, rounds: Int, useOriginal: Boolean = false, withVcd: Boolean = false) {
    def implName: String = if(useOriginal) "OriginalPicoRV32Mul" else "PicoRV32Mul"
    def name: String = s"$implName(stepsAtOnce = $stepsAtOnce, carryChain = $carryChain"
    def task: String = s"correctly $op $rounds different pairs of numbers"
    def gen(): PCPIModule = if(useOriginal) {
      new OriginalPicoRV32Mul(stepsAtOnce, carryChain)
    } else {
      new PicoRV32Mul(stepsAtOnce, carryChain)
    }
  }

  val allTests = Seq(
    TestConfig(1, 0, MUL,    100),
    TestConfig(1, 0, MULH,   100),
    TestConfig(1, 0, MULHU,  100),
    TestConfig(1, 0, MULHSU, 100),
  ) ++
  // try different step sizes
  (1 to 31).flatMap(s => allOps.map(TestConfig(s, 0, _, 10))) ++
  // try different carry chains != 0
  Seq(2,4,8,16,32,64).flatMap(c => Seq(1,3,7,19,31).flatMap(s => allOps.map(TestConfig(s, c, _, 10))))

  val quickRegressionsTests = Seq(
    TestConfig(1, 0, MUL,    40),
    TestConfig(1, 0, MULH,   40),
    TestConfig(1, 0, MULHU,  40),
    TestConfig(1, 0, MULHSU, 40),
    TestConfig(8, 0, MUL,    40),
    TestConfig(8, 0, MULH,   40),
    TestConfig(8, 0, MULHU,  40),
    TestConfig(8, 0, MULHSU, 40),
    TestConfig(1, 4, MUL,    40),
    TestConfig(1, 4, MULH,   40),
    TestConfig(1, 4, MULHU,  40),
    TestConfig(1, 4, MULHSU, 40),
  )

  def runTest(conf: TestConfig): Unit = {
    val annos = (if(conf.withVcd) withVcd else Seq()) ++ (if(conf.useOriginal) withVerilator else Seq())
    val random = new scala.util.Random(0)
    test(conf.gen()).withAnnotations(annos) { dut =>
      (0 until conf.rounds).foreach{ _ =>
        val (rs1, rs2) = (BigInt(32, random), BigInt(32, random))
        val rd = do_mul(conf.op, rs1, rs2)
        mulProtocol(dut.io, dut.clock, conf.op, rs1.U, rs2.U, rd.U)
      }
    }
  }

  def declareAndRunTest(conf: TestConfig): Unit = {
    conf.name should conf.task in { runTest(conf) }
  }

  quickRegressionsTests.foreach(declareAndRunTest)
  // allTests.foreach(declareAndRunTest)
}
