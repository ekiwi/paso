package fifo

import chisel3._
import chisel3.util._


class BasejumpFifoIO(val dataWidth: Int) extends Bundle {
  val dataIn = Input(UInt(dataWidth.W))
  val valid = Input(Bool())
  val pushDontPop = Input(Bool())
  val full = Output(Bool())
  val empty = Output(Bool())
  val dataOut = Output(UInt(dataWidth.W))
}

// based on https://github.com/bespoke-silicon-group/basejump_stl/blob/master/bsg_dataflow/bsg_fifo_1rw_large.v
class BasejumpFifo(val dataWidth: Int, val depth: Int) extends Module {
  require(isPow2(depth))
  val io = IO(new BasejumpFifoIO(dataWidth))

  val pointerWidth = log2Ceil(depth)

  val memWrite = io.pushDontPop && io.valid
  val memRead = !io.pushDontPop && io.valid
  val lastOpIsRead = RegInit(true.B)
  when(io.valid) { lastOpIsRead := memRead }

  // we simplified things quite a bit by requiring depth to be a power of two
  val readPointer = RegInit(0.U(pointerWidth.W))
  when(memRead) { readPointer := readPointer + 1.U }
  val writePointer = RegInit(0.U(pointerWidth.W))
  when(memWrite) { writePointer := writePointer + 1.U }

  val fifoEmpty = (readPointer === writePointer) && lastOpIsRead
  val fifoFull = (readPointer === writePointer) && !lastOpIsRead
  io.empty := fifoEmpty
  io.full := fifoFull

  val mem = SyncReadMem(depth, UInt(dataWidth.W))
  val memAddr = Mux(memWrite, writePointer, readPointer)
  val memPort = mem(memAddr)
  io.dataOut := DontCare
  when(memWrite) { memPort := io.dataIn }
  .elsewhen(memRead) { io.dataOut := memPort }

}

