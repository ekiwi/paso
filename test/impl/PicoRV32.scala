// rewrite of some parts of picorv32 in Chisel
// the original project can be found at https://github.com/cliffordwolf/picorv32

package impl

import chisel3._

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

class PicoRV32Mul(val stepsAtOnce: Int = 1, carryChain: Int = 4) extends PCPIModule {
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
  val doWait = RegNext(instrAnyMul)
  io.doWait := doWait
  val doWaitBuffer = RegNext(doWait)
  val mulStart = doWait && !doWaitBuffer // rising edge


  // carry save
  val state = Reg(new CarrySaveState)

  var (next_rs1, next_rs2 , next_rd, next_rdx) = (state.rs1, state.rs2, state.rd, state.rdx)
  (0 until stepsAtOnce).foreach { i =>
    val this_rs2 = Mux(next_rs1(0), next_rs2, 0.U)
    if(carryChain == 0) {
      val next_rdt = next_rd ^ next_rdx ^ this_rs2
      next_rdx = ((next_rd & next_rdx) | (next_rd & this_rs2) | (next_rdx & this_rs2)) << 1
      next_rd = next_rdt
    } else {
      throw new NotImplementedError("TODO: carry chain!")
    }
    next_rs1 = next_rs1 >> 1
    next_rs2 = next_rs2 << 1
  }

  val mulCounter = Reg(UInt(7.W))
  val mulWaiting = RegInit(true.B)
  val mulFinish = RegNext(!mulWaiting && mulCounter(6))
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
    state.rs1 := next_rs1
    state.rs2 := next_rs2
    state.rd  := next_rd
    state.rdx := next_rdx
    mulCounter := mulCounter - stepsAtOnce.U
    mulWaiting := mulCounter(6) === 1.U
  }

  io.wr := RegNext(mulFinish, init = false.B)
  io.ready := RegNext(mulFinish, init = false.B)
  val rdBuffer = Reg(chiselTypeOf(io.rd))
  when(mulFinish) { rdBuffer := Mux(instrAnyMulH, state.rd >> 32, state.rd) }
  io.rd := rdBuffer

}