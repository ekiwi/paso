// rewrite of some parts of picorv32 in Chisel
// the original project can be found at https://github.com/cliffordwolf/picorv32

package impl

import chisel3._
import chisel3.util._

/* Pico Co-Processor Interface (https://github.com/cliffordwolf/picorv32#pico-co-processor-interface-pcpi) */
class PCPI extends Bundle {
  val valid = Output(Bool())
  val insn = Output(UInt(32.W))
  val rs1 = Output(UInt(32.W))
  val rs2 = Output(UInt(32.W))
  val wr = Input(Bool())
  val rd = Input(UInt(32.W))
  val doWait = Input(Bool()).suggestName("wait")
  val ready = Input(Bool())
}

abstract class PCPIModule extends Module {
  val io = IO(Flipped(new PCPI))
}

class CarrySaveState extends Bundle {
  val rs1 = UInt(64.W)
  val rs2 = UInt(64.W)
  val rd = UInt(64.W)
  val rdx = UInt(64.W)
}

class CarrySaveStep(carryChain: Int = 4) extends Module {
  val io = IO(new Bundle {
    val in = Input(new CarrySaveState)
    val out = Output(new CarrySaveState)
  })

  val this_rs2 = Mux(io.in.rs1(0), io.in.rs2, 0.U)
  // calculates rd + rdx + this_rs2
  if(carryChain == 0) {
    io.out.rdx := ((io.in.rd & io.in.rdx) | (io.in.rd & this_rs2) | (io.in.rdx & this_rs2)) << 1
    io.out.rd := io.in.rd ^ io.in.rdx ^ this_rs2
  } else {
    val carry_res = (0 until 64 by carryChain).map { j =>
      val (msb, lsb) = (j + carryChain - 1, j)
      val tmp = io.in.rd(msb,lsb) +& io.in.rdx(msb,lsb) +& this_rs2(msb,lsb)
      val carry = tmp(carryChain) ## 0.U((carryChain-1).W)
      Seq(carry, tmp(carryChain-1,0))
    }.transpose
    io.out.rdx := carry_res(0).reverse.reduce((a,b) => a ## b) << 1
    io.out.rd := carry_res(1).reverse.reduce((a,b) => a ## b)
  }
  io.out.rs1 := io.in.rs1 >> 1
  io.out.rs2 := io.in.rs2 << 1
}



class PicoRV32Mul(val stepsAtOnce: Int = 1, carryChain: Int = 4) extends PCPIModule {
  require(stepsAtOnce >= 1 && stepsAtOnce <= 31)
  require(carryChain == 0 || 64 % carryChain == 0)
  // decoder
  def isMulInstr(kind: UInt) = io.valid && io.insn(6,0) === "b0110011".U && io.insn(31,25) === 1.U && io.insn(14,12) === kind
  val instrMul = RegNext(isMulInstr("b000".U))
  val instrMulH = RegNext(isMulInstr("b001".U))
  val instrMulHSU = RegNext(isMulInstr("b010".U))
  val instrMulHU = RegNext(isMulInstr("b011".U))
  val instrAnyMul = instrMul || instrMulH || instrMulHSU || instrMulHU
  val instrAnyMulH = instrMulH || instrMulHSU || instrMulHU
  val instrRs1Signed = instrMulH || instrMulHSU
  val instrRs2Signed = instrMulH

  // control logic
  val doWait = RegNext(instrAnyMul, init=false.B) // this register isn't resent in the original core
  io.doWait := doWait
  val doWaitBuffer = RegNext(doWait)
  val mulStart = doWait && !doWaitBuffer // rising edge

  // carry save chain
  val state = Reg(new CarrySaveState)
  val chain = Seq.tabulate(stepsAtOnce)(_ => Module(new CarrySaveStep(carryChain)))
  chain.head.io.in := state
  chain.iterator.sliding(2).withPartial(false).foreach { case Seq(a, b) => b.io.in := a.io.out }

  val mulCounter = Reg(UInt(7.W))
  val mulWaiting = RegInit(true.B)
  // this register isn't resent in the original core
  val mulFinish = RegNext(!mulWaiting && mulCounter(6), init=false.B)
  when(mulWaiting) {
    when(instrRs1Signed) { state.rs1 := io.rs1.asSInt().pad(64).asUInt() }
      .otherwise         { state.rs1 := io.rs1 }
    when(instrRs2Signed) { state.rs2 := io.rs2.asSInt().pad(64).asUInt() }
      .otherwise         { state.rs2 := io.rs2 }

    state.rd := 0.U
    state.rdx := 0.U
    mulCounter := Mux(instrAnyMulH, (63 - stepsAtOnce).U, (31 - stepsAtOnce).U)
    mulWaiting := !mulStart
  } .otherwise {
    state := chain.last.io.out
    mulCounter := mulCounter - stepsAtOnce.U
    mulWaiting := mulCounter(6) === 1.U
  }

  val mulFinishDelay = RegNext(mulFinish, init = false.B)
  io.wr := mulFinishDelay
  io.ready := mulFinishDelay
  val rdBuffer = Reg(chiselTypeOf(io.rd))
  when(mulFinish) { rdBuffer := Mux(instrAnyMulH, state.rd >> 32, state.rd) }
  io.rd := rdBuffer

}

class OriginalPicoRV32Mul(val stepsAtOnce: Int = 1, carryChain: Int = 4) extends PCPIModule {
  val bb = Module(new picorv32_pcpi_mul(stepsAtOnce, carryChain))
  bb.io.clk := clock
  bb.io.resetn := !reset.asUInt()
  bb.io.pcpi_valid := io.valid
  bb.io.pcpi_insn := io.insn
  bb.io.pcpi_rs1 := io.rs1
  bb.io.pcpi_rs2 := io.rs2
  io.wr := bb.io.pcpi_wr
  io.rd := bb.io.pcpi_rd
  io.doWait := bb.io.pcpi_wait
  io.ready := bb.io.pcpi_ready
}
class picorv32_pcpi_mul(val stepsAtOnce: Int = 1, carryChain: Int = 4) extends BlackBox(Map("STEPS_AT_ONCE" -> stepsAtOnce, "CARRY_CHAIN" -> carryChain)) with HasBlackBoxResource {
  val io = IO(new Bundle {
    val clk = Input(Clock())
    val resetn = Input(Bool())
    val pcpi_valid = Input(UInt(1.W))
    val pcpi_insn = Input(UInt(32.W))
    val pcpi_rs1 = Input(UInt(32.W))
    val pcpi_rs2 = Input(UInt(32.W))
    val pcpi_wr = Output(UInt(1.W))
    val pcpi_rd = Output(UInt(32.W))
    val pcpi_wait = Output(UInt(1.W))
    val pcpi_ready = Output(UInt(1.W))
  })
  addResource("/picorv32_pcpi_mul.v")
}