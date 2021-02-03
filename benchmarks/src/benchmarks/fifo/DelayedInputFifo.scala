// Copyright 2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package benchmarks.fifo

import chisel3._
import chisel3.util._


/** This Fifo is based on an interview question for a FV internship.
 *  Its enqueue interface allows the data to arrive at a variable latency.
 *
 * */
class DelayedInputQueue[D <: Data](val tpe: D, val entries: Int, val maxDelay: Int) extends Module {
  val delayWidth = log2Ceil(maxDelay + 1)

  val io = IO(new DelayedInputQueueIO(tpe, entries, delayWidth))

  val mem = SyncReadMem(entries, tpe)
  val count = RegInit(0.U(log2Ceil(entries + 1).W))


  // write interface
  val writeFuture = RegInit(0.U(maxDelay.W))

  val delayOneHot = 1.U << io.inDelay
  val inFired = io.inValid && io.inReady
  val writeImmediately = inFired && io.inDelay === 0.U

  val doWrite = writeFuture(0) || (inFired && io.inDelay === 0.U)


}

class DelayedInputQueueIO[T <: Data](private val dataType: T, val entries: Int, val delayWidth: Int) extends Bundle {
  // input interface
  val inValid = Input(Bool())
  val inReady = Output(Bool())
  val inDelay = Input(UInt(delayWidth.W))
  val inData = Input(dataType)

  // output interface
  val outValid = Output(Bool())
  val dequeue = Input(Bool())
  val outData = Output(dataType)

}