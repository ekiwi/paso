package fifo

import chisel3._
import chisel3.util._

class MannFifoIO(val dataWidth: Int) extends Bundle {
  val push = Input(Bool())
  val pop = Input(Bool())
  val data_in = Input(UInt(dataWidth.W))
  val full = Output(Bool())
  val empty = Output(Bool())
  val data_out = Output(UInt(dataWidth.W))
}

abstract class IsFifo extends Module { val io: MannFifoIO ; val width: Int ; val depth: Int ; val readDelay: Int }

// rewrite of Makai Mann's circular fifo in Chisel
class CircularPointerFifo(val width: Int, val depth: Int, val readDelay: Int = 0, fixed: Boolean = false) extends IsFifo {
  require(isPow2(depth))
  require(readDelay == 0 || readDelay == 1)
  val io = IO(new MannFifoIO(width))

  val counter_init = 0.U((log2Ceil(depth) + 1).W)

  val cnt = RegInit(counter_init)
  cnt := cnt + io.push - io.pop

  val pointer_width = if(fixed) log2Ceil(depth) else log2Ceil(depth) + 1
  val pointer_init = 0.U(pointer_width.W)

  val wrPtr = RegInit(pointer_init)
  wrPtr := wrPtr + io.push

  val rdPtr = RegInit(pointer_init)
  rdPtr := rdPtr + io.pop

  io.empty := cnt === 0.U
  io.full := cnt === depth.U

  val entries = Mem(depth, UInt(width.W))
  val input_data = Mux(io.push, io.data_in, entries.read(wrPtr))
  entries.write(wrPtr, input_data)

  if(readDelay == 0) {
    io.data_out := entries.read(rdPtr)
  } else {
    io.data_out := RegNext(entries.read(rdPtr))
  }

}
