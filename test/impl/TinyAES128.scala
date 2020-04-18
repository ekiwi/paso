// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

// Chisel port of the OpenCores TinyAES core


package impl

import chisel3._
import chisel3.util._

object Utils {
  def split(signal: UInt, by: Int): Vec[UInt] = {
    val subWidth = signal.getWidth / by
    require(subWidth * by == signal.getWidth)
    VecInit(Seq.tabulate(by)(ii => signal(subWidth*(ii+1)-1, subWidth*ii)))
  }
}

class TinyAES128 extends Module {
  val io = IO(new Bundle {
    val state = UInt(128.W)
    val key = UInt(128.W)
  })
}

// https://en.wikipedia.org/wiki/AES_key_schedule
class ExpandKey128(rcon: UInt) extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(128.W))
    val out = Output(UInt(128.W))
    val outDelayed = Output(UInt(128.W))
  })
  val k = Utils.split(io.in, 4)
  val v0 = k(3)(31,24) ^ rcon ## k(3)(23,0)
  val v1 = v0 ^ k(2)
  val v2 = v1 ^ k(1)
  val v3 = v2 ^ k(0)

  val k0a = RegNext(v0)
  val k1a = RegNext(v1)
  val k2a = RegNext(v2)
  val k3a = RegNext(v3)

  val S4_0 = Module(new S4)
  S4_0.io.in := k(0)(23,0) ## k(0)(31,24)
  val k4a = S4_0.io.out

  val k0b = k0a ^ k4a
  val k1b = k1a ^ k4a
  val k2b = k2a ^ k4a
  val k3b = k3a ^ k4a

  io.out := k0b ## k1b ## k2b ## k3b
  io.outDelayed := RegNext(io.out)
}

class TableLookup extends Module {
  val io = IO(new Bundle {
    val state = Input(UInt(32.W))
    val p = Output(Vec(4, UInt(32.W)))
  })
  val b = Utils.split(io.state, 4)
  val t = Seq.tabulate(4)(_ => Module(new T))
  t.zip(b).foreach{case (t,b) => t.io.in := b}
  io.p(0) := t(3).io.out( 7,0) ## t(3).io.out(31, 8)
  io.p(1) := t(2).io.out(15,0) ## t(2).io.out(31,16)
  io.p(2) := t(1).io.out(23,0) ## t(1).io.out(31,24)
  io.p(3) := t(0).io.out
}

class IOBundle(inWidth: Int, outWidth: Int) extends Bundle {
  val in = Input(UInt(inWidth.W))

}

class S4 extends Module {
  val io = IO(new Bundle { val in = Input(UInt(32.W)) ; val out = UInt(32.W) })
  val S = Seq.tabulate(4)(_ => Module(new S))
  Utils.split(io.in, 4).zip(S).foreach { case (i, s) => s.io.in := i }
  io.out := S.map(_.io.out).reduce((a,b) => a ## b)
}

class T extends Module {
  val io = IO(new Bundle { val in = UInt(8.W) ; val out = UInt(32.W) })
  val s0 = Module(new S)
  s0.io.in := io.in
  val s4 = Module(new xS)
  s4.io.in := io.in
  io.out := s0.io.out ## s0.io.out ## (s0.io.out ^ s4.io.out) ## s4.io.out
}

class S extends Module {
  val io = IO(new Bundle { val in = UInt(8.W) ; val out = UInt(8.W) })
}
class xS extends Module {
  val io = IO(new Bundle { val in = UInt(8.W) ; val out = UInt(8.W) })
}