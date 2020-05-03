// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>
package paso

import chisel3._
import chisel3.experimental.{ChiselAnnotation, IO, annotate}
import chisel3.util.log2Ceil
import firrtl.annotations.{ReferenceTarget, SingleTargetAnnotation}

import scala.collection.mutable

/** Specifies a Chisel Module `IM` by binding it to an untimed model `SM` through protocols. */
abstract class ProtocolSpec[S <: UntimedModule] {
  val spec: S
  val protos = new mutable.ArrayBuffer[Protocol]()
  def protocol[IO <: Data](meth: NMethod)(io: IO)(gen: (Clock, IO) => Unit): Unit =
    protos.append(NProtocol(chiselTypeOf(io), meth, gen))
  def protocol[O <: Data, IO <: Data](meth: OMethod[O])(io: IO)(gen: (Clock, IO, O) => Unit): Unit =
    protos.append(OProtocol(chiselTypeOf(io), meth, gen))
  def protocol[I <: Data, IO <: Data](meth: IMethod[I])(io: IO)(gen: (Clock, IO, I) => Unit): Unit =
    protos.append(IProtocol(chiselTypeOf(io), meth, gen))
  def protocol[I <: Data, O <: Data, IO <: Data](meth: IOMethod[I, O])(io: IO)(gen: (Clock, IO, I,O) => Unit): Unit =
    protos.append(IOProtocol(chiselTypeOf(io), meth, gen))


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

trait Protocol {
  def methodName: String
  def generate(prefix: String, clock: Clock): Unit
}
trait ProtocolHelper extends MethodBodyHelper {
  protected def io[IO <: Data](ioType: IO): IO = IO(Flipped(ioType)).suggestName("io")
}
case class NProtocol[IO <: Data](ioType: IO, meth: NMethod, impl: (Clock, IO) => Unit) extends Protocol with ProtocolHelper {
  override def methodName = meth.gen.name
  override def generate(prefix: String, clock: Clock): Unit = impl(clock, io(ioType))
}
case class IProtocol[IO <: Data, I <: Data](ioType: IO, meth: IMethod[I], impl: (Clock, IO, I) => Unit) extends Protocol with ProtocolHelper  {
  override def methodName = meth.gen.name
  override def generate(prefix: String, clock: Clock): Unit = impl(clock, io(ioType), makeInput(meth.inputType, prefix))
}
case class OProtocol[IO <: Data, O <: Data](ioType: IO, meth: OMethod[O], impl: (Clock, IO, O) => Unit) extends Protocol with ProtocolHelper  {
  override def methodName = meth.gen.name
  override def generate(prefix: String, clock: Clock): Unit = impl(clock, io(ioType), makeOutput(meth.outputType, prefix))
}
case class IOProtocol[IO <: Data, I <: Data, O <: Data](ioType: IO, meth: IOMethod[I,O], impl: (Clock, IO, I, O) => Unit) extends Protocol with ProtocolHelper  {
  override def methodName = meth.gen.name
  override def generate(prefix: String, clock: Clock): Unit = {
    impl(clock, io(ioType), makeInput(meth.inputType, prefix), makeOutput(meth.outputType, prefix))
  }
}

abstract class ProofCollateral[I <: RawModule, S <: UntimedModule](impl: I, spec: S) {

  val invs = new mutable.ArrayBuffer[I => Unit]()
  def invariances(gen: I => Unit): Unit = invs.append(gen)


  val maps = new mutable.ArrayBuffer[(I,S) => Unit]()
  def mapping(gen: (I, S) => Unit): Unit = maps.append(gen)

  // replace default chisel assert
  def assert(cond: => Bool): Unit = {
    val w = Wire(Bool()).suggestName("assert")
    w := cond
    annotate(new ChiselAnnotation { override def toFirrtl = AssertAnnotation(w.toTarget) })
  }

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


case class AssertAnnotation(target: ReferenceTarget) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}

case class ExpectAnnotation(target: ReferenceTarget) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}

case class StepAnnotation(target: ReferenceTarget) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}

case class MemToVecAnnotation(target: ReferenceTarget, mem: ReferenceTarget, depth: BigInt, width: Int) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}

case class MemEqualAnnotation(target: ReferenceTarget, mem0: ReferenceTarget, mem1: ReferenceTarget, depth: BigInt, width: Int) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}

case class ForallStartAnnotation(target: ReferenceTarget, start: Int, end: Int) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}

case class ForallEndAnnotation(target: ReferenceTarget) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}