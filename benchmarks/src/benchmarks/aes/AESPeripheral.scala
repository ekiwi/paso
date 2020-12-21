package benchmarks.aes

import chisel3._
import chisel3.experimental.ChiselEnum
import chisel3.util._

// this is a Chisel reimplementation of the `aes_top` module from the
// following ILA example:
// https://github.com/PrincetonUniversity/IMDb/blob/master/accls/AES/AES-ILA-RTL/verilog/aes_top.v

class BusIO extends Bundle {
  val addr = Output(UInt(16.W))
  val dataOut = Output(UInt(8.W))
  val dataIn = Input(UInt(8.W))
  val ack = Input(Bool())
  val stb = Output(Bool())
  val wr = Output(Bool())
}

class AESPeripheral extends Module {
  val io = IO(new Bundle {
    val proc = Flipped(new BusIO)
    val xram = new BusIO
  })

  val AddrStart = "hff00".U
  val RegStart = AddrStart
  val RegState = AddrStart + 1.U
  val RegAddr = AddrStart + 2.U
  val RegLen = AddrStart + 4.U
  val RegKey0 = AddrStart + "h10".U
  val RegCtr = AddrStart + "h20".U
  val AddrEnd = AddrStart + "h30".U

  object State extends ChiselEnum { val Idle, ReadData, Operate, WriteData = Value }

  val inAddrRange = io.proc.addr >= AddrStart && io.proc.addr < AddrEnd
  io.proc.ack := io.proc.stb && inAddrRange

  val selRegStart = io.proc.addr === RegStart
  val selRegState = io.proc.addr === RegState
  val selRegAddr  = io.proc.addr.head(15) === RegAddr.head(15)
  val selRegLen   = io.proc.addr.head(15) === RegLen.head(15)
  val selRegKey0  = io.proc.addr.head(12) === RegKey0.head(12)
  val selRegCtr   = io.proc.addr.head(12) === RegCtr.head(12)

  val aesState = RegInit(State.Idle)

  io.proc.dataIn := MuxCase(0.U, Seq(
    selRegState -> aesState,
    selRegAddr -> aesAddrDataOut,
    selRegLen -> aesLenDataOut,
    selRegCtr -> aesCtrDataOut,
    selRegKey0 -> aesKey0DataOut
  ))

  val writeEnable = io.proc.wr && aesState === State.Idle
  val (aesAddrDataOut, aesRegOpAddr) = ControlAndStatusRegister("opAddr", 2, selRegAddr, writeEnable, io.proc.addr, io.proc.dataIn)
  val (aesLenDataOut, aesRegOpLen)   = ControlAndStatusRegister("opLen",  2, selRegLen,  writeEnable, io.proc.addr, io.proc.dataIn)
  val (aesCtrDataOut, aesRegCtr)     = ControlAndStatusRegister("key0",   2, selRegKey0, writeEnable, io.proc.addr, io.proc.dataIn)
  val (aesKey0DataOut, aesRegKey0)   = ControlAndStatusRegister("ctr",    2, selRegCtr,  writeEnable, io.proc.addr, io.proc.dataIn)

  // writing a 1 to bit0 of the start register triggers an operation
  val startOp = selRegStart && io.proc.dataIn(0) && writeEnable


  val operatedBytesCount = RegInit(0.U(16.W))
  val blockCounter = RegInit(0.U(16.W))
  val byteCounter = RegInit(0.U(4.W))

  val lastByteAcked = byteCounter === 15.U && io.xram.ack
  val moreBlocks = lastByteAcked && aesState === State.WriteData && (operatedBytesCount + 16.U < aesRegOpLen)

  when(startOp) {
    operatedBytesCount := 0.U
    blockCounter := 0.U
  } .elsewhen(lastByteAcked && aesState === State.WriteData) {
    operatedBytesCount := operatedBytesCount + 16.U // seems like a waste of precious lsbs :(
    when(operatedBytesCount + 16.U < aesRegOpLen) {
      blockCounter := blockCounter + 16.U
    }
  }

  when(startOp) {
    byteCounter := 0.U
  } .elsewhen(io.xram.ack) {
    byteCounter := byteCounter + 1.U
  }

  // connect xram
  io.xram.addr := aesRegOpAddr + blockCounter + byteCounter
  io.xram.stb := aesState === State.ReadData || aesState === State.WriteData
  io.xram.wr := aesState === State.WriteData

  // state machine
  val aesDone = Wire(Bool())
  switch(aesState) {
    is(State.Idle) { when(startOp) { aesState := State.ReadData } }
    is(State.ReadData) { when(lastByteAcked) { aesState := State.Operate } }
    is(State.Operate) { when(aesDone) { aesState := State.WriteData} }
    is(State.WriteData) {
      when(lastByteAcked) {
        aesState := Mux(moreBlocks, State.ReadData, State.Idle)
      }
    }
  }

}

class ControlAndStatusRegisterIO(val bytes: Int) extends Bundle {
  require(bytes > 1)
  val enable = Input(Bool())
  val write = Input(Bool())
  val addr = Input(UInt(log2Ceil(bytes).W))
  val dataIn = UInt(8.W)
  val dataOut = UInt(8.W)
  val parallelOut = UInt((8*bytes).W)
}

class ControlAndStatusRegister(bytes: Int) extends Module {
  val io = IO(new ControlAndStatusRegisterIO(bytes))
  val reg = RegInit(VecInit(Seq.tabulate(bytes)(_ => 0.U(8.W))))

  io.parallelOut := reg.asUInt()
  io.dataOut := reg(io.addr)

  val writeEnable = io.enable && io.write
  (0 until bytes).foreach { ii =>
    val wr = (writeEnable && io.addr === ii.U).suggestName(s"wr$ii")
    reg(ii) := Mux(wr, io.dataIn, reg(ii))
  }
}

object ControlAndStatusRegister {
  def apply(name: String, bytes: Int, sel: Bool, writeEnable: Bool, addr: UInt, dataIn: UInt): (UInt, UInt) = {
    val m = Module(new ControlAndStatusRegister(bytes))
    m.io.enable := sel
    m.io.write := sel && writeEnable // all of this is a little redundant
    m.io.addr := addr
    m.io.dataIn := dataIn
    (m.io.dataOut, m.io.parallelOut)
  }
}