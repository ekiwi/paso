// Copyright 2020 The Regents of the University of California
// released under BSD 2-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package untimed

import org.scalatest.flatspec.AnyFlatSpec
import paso._
import chisel3._

class RiscVSpec extends UntimedModule {
  val reg = Mem(32, UInt(32.W)) // reg(0) remains unused

  private def readReg(addr: UInt): UInt = {
    require(addr.getWidth == 5)
    Mux(addr === 0.U, 0.U, reg.read(addr))
  }

  private def updateReg(addr: UInt, data: UInt): Unit = {
    require(addr.getWidth == 5)
    require(data.getWidth == 32)
    when(addr =/= 0.U) { reg.write(addr, data) }
  }

  private def rType(in: RTypeIO, op: (UInt, UInt) => UInt): Unit =
    updateReg(in.rd, op(readReg(in.rs1), readReg(in.rs2)))
  private def iType(in: ITypeIO, op: (UInt, UInt) => UInt): Unit =
    updateReg(in.rd, op(readReg(in.rs1), in.decodeImm))

  val add = fun("add").in(new RTypeIO)(rType(_, (a,b) => a + b))
  val sub = fun("sub").in(new RTypeIO)(rType(_, (a,b) => a - b))
  val addi = fun("addi").in(new ITypeIO)(iType(_, (a,b) => a + b))
}

class RTypeIO extends Bundle {
  val rs1 = UInt(5.W)
  val rs2 = UInt(5.W)
  val rd = UInt(5.W)
  def toInstruction(funct7: UInt, funct3: UInt, opcode: UInt): UInt = {
    funct7.pad(7) ## rs2 ## rs1 ## funct3.pad(3) ## rd ## opcode.pad(7)
  }
}

class ITypeIO extends Bundle {
  val imm = SInt(12.W)
  val rs1 = UInt(5.W)
  val rd = UInt(5.W)
  def decodeImm: UInt = imm.pad(32).asUInt()
  def toInstruction(funct3: UInt, opcode: UInt): UInt = {
    imm.asUInt() ## rs1 ## funct3.pad(3) ## rd ## opcode.pad(7)
  }
}

class CompileRiscVSpec extends AnyFlatSpec {
  behavior of "RiscVSpec"

  // many Chisel/Paso errors are only caught when elaborating
  it should "correctly elaborate" in {
    val spec = UntimedModule(new RiscVSpec)
    // println(spec.getFirrtl.circuit.serialize)
  }

}