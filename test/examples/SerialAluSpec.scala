// Copyright 2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package examples

import org.scalatest.flatspec.AnyFlatSpec
import chisel3._
import chisel3.experimental.ChiselEnum
import paso._

class AluModel extends UntimedModule {
  val add = fun("add").in(new AluArgs).out(UInt(32.W)) { (in, rd) =>
    rd := in.rs1 + in.rs2
  }
  val sub = fun("sub").in(new AluArgs).out(UInt(32.W)) { (in, rd) =>
    rd := in.rs1 - in.rs2
  }
}

class AluArgs extends Bundle {
  val rs1 = UInt(32.W)
  val rs2 = UInt(32.W)
}

class SerialAluProtocols(impl: SerialAlu) extends ProtocolSpec[AluModel] {
  val spec = new AluModel

  private def calculate(clock: Clock, io: AluIO, conf: DecodeToAluIO => Unit, rs1: UInt, rs2: UInt, rd: UInt) {
    io.count.count0.poke(false.B)
    io.count.enabled.poke(false.B)
    clock.step()
    io.count.count0.poke(true.B)
    io.count.enabled.poke(true.B)
    io.decode.opBIsRS2.poke(true.B)
    conf(io.decode)
    // bit0
    io.data.rs1.poke(rs1(0))
    io.data.rs2.poke(rs2(0))
    io.data.rd.expect(rd(0))
    clock.step()
    io.count.count0.poke(false.B)
    // bit1...bit31
    (1 until 32).foreach { ii =>
      io.data.rs1.poke(rs1(ii))
      io.data.rs2.poke(rs2(ii))
      io.data.rd.expect(rd(ii))
      clock.step()
    }
  }


  private def add(decode: DecodeToAluIO) { decode.doSubtract.poke(false.B) ; decode.rdSelect.poke(Result.Add) }
  private def sub(decode: DecodeToAluIO) { decode.doSubtract.poke(true.B)  ; decode.rdSelect.poke(Result.Add) }

  protocol(spec.add)(impl.io) { (clock, io, in, rd) => calculate(clock, io, add, in.rs1, in.rs2, rd) }
  protocol(spec.sub)(impl.io) { (clock, io, in, rd) => calculate(clock, io, sub, in.rs1, in.rs2, rd) }
}





class SerialAluSpec extends AnyFlatSpec with PasoTester  {
  behavior of "SerialAlu"

  it should "pass some cycles of BMC" in {
    test(new SerialAlu)(new SerialAluProtocols(_)).bmc(40)
  }

  it should "pass some cycles of random testing" in {
    test(new SerialAlu)(new SerialAluProtocols(_)).randomTest(40 * 1000)
  }

  it should "faile BMC w/ bug #1" in {
    assertThrows[AssertionError] {
      test(new SerialAlu(enableBug = 1))(new SerialAluProtocols(_)).bmc(40)
    }
  }

  it should "fail random testing w/ bug #1" in {
    assertThrows[AssertionError] {
      (0 until 40).foreach { seed =>
        test(new SerialAlu(enableBug = 1))(new SerialAluProtocols(_)).randomTest(k = 1000, seed = Some(seed))
      }
    }
  }
}




object BooleanOperation extends ChiselEnum {
  val Xor = Value(0.U(2.W))
  val Eq  = Value(1.U(2.W))
  val Or  = Value(2.U(2.W))
  val And = Value(3.U(2.W))
}

object Result extends ChiselEnum {
  val None  = Value("b0000".U(4.W))
  val Add   = Value("b0001".U(4.W))
  val Shift = Value("b0010".U(4.W))
  val Lt    = Value("b0100".U(4.W))
  val Bool  = Value("b1000".U(4.W))
}

class AluDataIO extends Bundle {
  val rs1 = Input(UInt(1.W))
  val rs2 = Input(UInt(1.W))
  val imm = Input(UInt(1.W))
  val buffer = Input(UInt(1.W))
  val rd = Output(UInt(1.W))
}


class CountIO extends Bundle {
  val enabled = Input(Bool())
  val init = Input(Bool())
  val count0 = Input(Bool())
  val done = Input(Bool())
}

class StateToAluIO extends Bundle {
  val shiftAmountEnable = Output(Bool())
  val shiftDone = Input(Bool())
}

class DecodeToAluIO extends Bundle {
  val doSubtract = Output(Bool())
  val boolOp = Output(BooleanOperation())
  val cmpEqual = Output(Bool())
  val cmpUnsigned = Output(Bool())
  val shiftSigned = Output(Bool())
  val shiftRight = Output(Bool())
  val rdSelect = Output(Result())
  val opBIsRS2 = Output(Bool()) // instead of immediate (op_b_source)
  val cmpResult = Input(Bool())
}

class AluIO extends Bundle {
  val decode = Flipped(new DecodeToAluIO)
  val data = new AluDataIO()
  val count = new CountIO()
  val state = Flipped(new StateToAluIO)
}

/** based on the ALU from the serv processor */
class SerialAlu(enableBug: Int = 0) extends Module {
  val io = IO(new AluIO)

  val operandB = Mux(io.decode.opBIsRS2, io.data.rs2, io.data.imm)

  // ~b + 1 (negate B operand)
  val plus1 = io.count.count0
  val negativeBCarry = Reg(UInt(1.W))
  val negativeBCarryAndResult = ~operandB +& plus1 + negativeBCarry
  negativeBCarry := io.count.enabled & negativeBCarryAndResult(1)
  if(enableBug == 1) {
    negativeBCarry := negativeBCarryAndResult(1)
  }
  val negativeB = negativeBCarryAndResult(0)


  // adder
  val addB = Mux(io.decode.doSubtract, negativeB, operandB)
  val addCarry = Reg(UInt(1.W))
  val addCarryNextAndResult = io.data.rs1 +& addB + addCarry
  addCarry := io.count.enabled & addCarryNextAndResult(1)
  val resultAdd = addCarryNextAndResult(0)

  // shifter
  val shiftAmountSerial = Mux(io.decode.shiftRight, operandB, negativeB)
  val shiftAmount = Reg(UInt(5.W))
  val shift = Module(new SerialShift)
  shift.io.load := io.count.init
  shift.io.shiftAmount := shiftAmount
  val shiftAmountMSB = Reg(UInt(1.W))
  when(io.state.shiftAmountEnable) {
    shiftAmountMSB := negativeB
    shiftAmount := shiftAmountSerial ## shiftAmount(4,1)
  }
  shift.io.shamt_msb := shiftAmountMSB
  shift.io.signbit := io.decode.shiftSigned & io.data.rs1
  shift.io.right := io.decode.shiftRight
  shift.io.d := io.data.buffer
  io.state.shiftDone := shift.io.done
  val resultShift = shift.io.q

  // equality
  val equal = io.data.rs1 === operandB
  val equalBuf = Reg(UInt(1.W))
  val resultEqual = equal & equalBuf
  equalBuf := resultEqual | ~(io.count.enabled)

  // less then
  val ltBuf = Reg(UInt(1.W))
  val ltSign = io.count.done & !io.decode.cmpUnsigned
  val resultLt = Mux(equal, ltBuf, operandB ^ ltSign)
  ltBuf := resultLt & io.count.enabled
  val resultLtBuf = Reg(UInt(1.W))
  when(io.count.enabled) { resultLtBuf := resultLt}

  io.decode.cmpResult := Mux(io.decode.cmpEqual, resultEqual, resultLt)

  // boolean operations
  val BoolLookupTable = "h8e96".U
  val resultBool = BoolLookupTable(io.decode.boolOp.asUInt() ## io.data.rs1 ## operandB)

  // results
  io.data.rd :=
    (io.decode.rdSelect.asUInt()(0) & resultAdd)           |
      (io.decode.rdSelect.asUInt()(1) & resultShift)         |
      (io.decode.rdSelect.asUInt()(2) & resultLtBuf & plus1) |
      (io.decode.rdSelect.asUInt()(3) & resultBool)
}

class SerialShift extends Module {
  val io = IO(new Bundle {
    val load = Input(Bool())
    val shiftAmount = Input(UInt(5.W))
    val shamt_msb = Input(UInt(1.W))
    val signbit = Input(UInt(1.W))
    val right = Input(Bool())
    val done = Output(Bool())
    val d = Input(UInt(1.W))
    val q = Output(UInt(1.W))
  })

  val cnt = Reg(UInt(6.W))
  val signbit = Reg(UInt(1.W))
  val wrapped = RegNext(cnt.head(1) | io.shamt_msb & !io.right)

  when(io.load) {
    cnt := 0.U
    signbit := io.signbit & io.right
  }.otherwise {
    cnt := cnt + 1.U
  }

  io.done := cnt(4, 0) === io.shiftAmount
  io.q := Mux(io.right =/= wrapped, io.d, signbit)
}