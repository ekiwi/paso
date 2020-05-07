package fifo

import chisel3._
import chisel3.util._

// rewrite of Makai Mann's shift register based fifo in Chisel
class ShiftRegisterFifo(val width: Int, val depth: Int, fixed: Boolean = false) extends IsFifo {
  require(isPow2(depth))
  val io = IO(new FifoIO(width))

  val counter_init = 0.U((log2Ceil(depth) + 1).W)

  val count = RegInit(counter_init)
  count := count + io.push - io.pop

  io.empty := count === 0.U
  io.full  := count >= depth.U

  val next_value = Seq.fill(depth)(Wire(UInt(width.W)))
  val entries = (0 until depth).map { ii =>
    val reg = RegInit(0.U(width .W))
    when(io.pop || (io.push && (count === ii.U))) {
      reg := next_value(ii)
    }
    reg
  }

  val nv =if(fixed) next_value else next_value.dropRight(1) // BUG: short by one
  nv.zipWithIndex.foreach { case (next, j) =>
    val not_pushed = entries.lift(j+1).map(Mux(io.pop, _, 0.U)).getOrElse(0.U)
    next := Mux(io.push && (count - io.pop) === j.U, io.data_in, not_pushed)
  }

  io.data_out := entries.head
}
