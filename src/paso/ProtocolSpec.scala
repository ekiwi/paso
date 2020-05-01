// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>
package paso

import chisel3._
import chisel3.experimental.{ChiselAnnotation, annotate}
import chisel3.util.log2Ceil
import scala.collection.mutable

/** Specifies a Chisel Module `IM` by binding it to an untimed model `SM` through protocols. */
abstract class ProtocolSpec {
  // TODO: can we get rid of impl + spec fields? are they needed?
  val impl: RawModule
  val spec: UntimedModule
  val protos = new mutable.ArrayBuffer[Protocol]()
  def protocol[IO <: Data](meth: NMethod)(io: IO)(gen: (Clock, IO) => Unit): Unit =
    protos.append(NProtocol(chiselTypeOf(io), meth, gen))
  def protocol[O <: Data, IO <: Data](meth: OMethod[O])(io: IO)(gen: (Clock, IO, O) => Unit): Unit =
    protos.append(OProtocol(chiselTypeOf(io), meth, gen))
  def protocol[I <: Data, IO <: Data](meth: IMethod[I])(io: IO)(gen: (Clock, IO, I) => Unit): Unit =
    protos.append(IProtocol(chiselTypeOf(io), meth, gen))
  def protocol[I <: Data, O <: Data, IO <: Data](meth: IOMethod[I, O])(io: IO)(gen: (Clock, IO, I,O) => Unit): Unit =
    protos.append(IOProtocol(chiselTypeOf(io), meth, gen))

  // replace default chisel assert
  def assert(cond: => Bool): Unit = {
    val w = Wire(Bool()).suggestName("assert")
    w := cond
    annotate(new ChiselAnnotation { override def toFirrtl = AssertAnnotation(w.toTarget) })
  }


  // TODO: support more than just UInt
  implicit class testableData[T <: UInt](x: T) {
    def set(value: T): Unit = {
      x := value
    }
    def poke(value: T): Unit = set(value)
    def set(value: DontCare.type): Unit = {
      x := value
    }
    def poke(value: DontCare.type): Unit = set(value)
    def get(): T = x
    def peek(): T = get()
    def expect(value: T): Unit = {
      val w = Wire(Bool()).suggestName("expect")
      w := x === value
      annotate(new ChiselAnnotation { override def toFirrtl = ExpectAnnotation(w.toTarget) })
    }
  }

  implicit class testableClock(x: Clock) {
    def step(): Unit = {
      val w = Wire(Bool()).suggestName("step")
      annotate(new ChiselAnnotation { override def toFirrtl = StepAnnotation(w.toTarget) })
    }
  }

  def do_while(cond: => Bool, max: Int)(block: => Unit) = {
    require(max > 0, "Loop bounds must be greater zero!")
    require(max < 1024, "We currently do not support larger loop bounds!")
    unroll(cond, max, block)
  }

  private def unroll(cond: => Bool, max: Int, body: => Unit): Unit = if(max > 0) {
    when(cond) {
      body
      unroll(cond, max-1, body)
    }
  } else {
    // ???
  }
}

abstract class InductiveProof[IM <: RawModule, SM <: UntimedModule] {
  def impl: IM
  def spec: ProtocolSpec[IM, SM]

  val invs = new mutable.ArrayBuffer[IM => Unit]()
  def invariances(gen: IM => Unit): Unit = invs.append(gen)


  val maps = new mutable.ArrayBuffer[(IM,SM) => Unit]()
  def mapping(gen: (IM, SM) => Unit): Unit = maps.append(gen)

  implicit class comparableMem[T <: UInt](x: Mem[T]) {
    def ===(y: Mem[T]): Bool = {
      require(x.length > 0)
      require(x.length == y.length)
      val w = Wire(Bool()).suggestName(s"eq($x, $y)")
      dontTouch(w)
      val depth = x.length
      val width = x.t.getWidth
      annotate(new ChiselAnnotation { override def toFirrtl = MemEqualAnnotation(w.toTarget, x.toTarget, y.toTarget, depth, width) })
      w
    }
  }

  def forall(range: Range)(block: UInt => Unit): Unit = {
    require(range.step == 1, s"Only step size 1 supported: $range")
    require(range.start >= 0 && range.end >= 0, s"Only positive ranges supported: $range")
    require(range.start <= range.end)

    // generate a wire to represent the universally quantified variable
    val bits = log2Ceil(range.end)
    val ii = Wire(UInt(bits.W)).suggestName(s"ii_${range.start}_to_${range.end-1}")
    dontTouch(ii)
    annotate(new ChiselAnnotation { override def toFirrtl = ForallStartAnnotation(ii.toTarget, range.start, range.end) })

    // generate the block code once
    block(ii)

    // mark the end of the block (important: this only works if we do not run too many passes / optimizations)
    val end = WireInit(false.B).suggestName("forall_end")
    dontTouch(end)
    annotate(new ChiselAnnotation { override def toFirrtl = ForallEndAnnotation(end.toTarget) })
  }
}