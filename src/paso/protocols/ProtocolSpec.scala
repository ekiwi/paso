// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>
package paso.protocols

import chisel3._
import chisel3.experimental.{ChiselAnnotation, IO, annotate}
import firrtl.annotations.{ReferenceTarget, SingleTargetAnnotation}
import paso.UntimedModule
import paso.untimed.{IMethod, IOMethod, NMethod, OMethod}

import scala.collection.mutable

/** Specifies a Chisel Module `IM` by binding it to an untimed model `SM` through protocols. */
abstract class ProtocolSpec[+S <: UntimedModule] {
  val spec: S
  val stickyInputs: Boolean = true
  val protos = new mutable.ArrayBuffer[Protocol]()
  def protocol[IO <: Data](meth: NMethod)(io: IO)(gen: (Clock, IO) => Unit): Unit =
    protos.append(NProtocol(chiselTypeOf(io), meth, gen, stickyInputs))
  def protocol[O <: Data, IO <: Data](meth: OMethod[O])(io: IO)(gen: (Clock, IO, O) => Unit): Unit =
    protos.append(OProtocol(chiselTypeOf(io), meth, gen, stickyInputs))
  def protocol[I <: Data, IO <: Data](meth: IMethod[I])(io: IO)(gen: (Clock, IO, I) => Unit): Unit =
    protos.append(IProtocol(chiselTypeOf(io), meth, gen, stickyInputs))
  def protocol[I <: Data, O <: Data, IO <: Data](meth: IOMethod[I, O])(io: IO)(gen: (Clock, IO, I,O) => Unit): Unit =
    protos.append(IOProtocol(chiselTypeOf(io), meth, gen, stickyInputs))


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
    def expect(value: T): Unit = { assert(x === value) }
  }

  implicit class testableClock(x: Clock) {
    def step(fork: Boolean = false): Unit = {
      val w = Wire(Bool()).suggestName("step")
      annotate(new ChiselAnnotation { override def toFirrtl = StepAnnotation(w.toTarget, fork) })
    }
    def stepAndFork(): Unit = step(true)
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
    assert(!cond)
  }

  // replace default chisel assert
  private def assert(cond: => Bool): Unit = chisel3.experimental.verification.assert(cond)
}

trait Protocol {
  def methodName: String
  def generate(clock: Clock): Unit
  val stickyInputs: Boolean
}
trait ProtocolHelper {
  protected def implIO[IO <: Data](ioType: IO): IO = IO(Flipped(ioType)).suggestName("io")
  protected def methodArg[I <: Data](argType: I): I = IO(Input(argType)).suggestName("arg")
  protected def methodRet[O <: Data](retType: O): O = IO(Input(retType)).suggestName("ret")
}
case class NProtocol[IO <: Data](ioType: IO, meth: NMethod, impl: (Clock, IO) => Unit, stickyInputs: Boolean) extends Protocol with ProtocolHelper {
  override def methodName = meth.name
  override def generate(clock: Clock): Unit = impl(clock, implIO(ioType))
}
case class IProtocol[IO <: Data, I <: Data](ioType: IO, meth: IMethod[I], impl: (Clock, IO, I) => Unit, stickyInputs: Boolean) extends Protocol with ProtocolHelper  {
  override def methodName = meth.name
  override def generate(clock: Clock): Unit = impl(clock, implIO(ioType), methodArg(meth.inputType))
}
case class OProtocol[IO <: Data, O <: Data](ioType: IO, meth: OMethod[O], impl: (Clock, IO, O) => Unit, stickyInputs: Boolean) extends Protocol with ProtocolHelper  {
  override def methodName = meth.name
  override def generate(clock: Clock): Unit = impl(clock, implIO(ioType), methodRet(meth.outputType))
}
case class IOProtocol[IO <: Data, I <: Data, O <: Data](ioType: IO, meth: IOMethod[I,O], impl: (Clock, IO, I, O) => Unit, stickyInputs: Boolean) extends Protocol with ProtocolHelper  {
  override def methodName = meth.name
  override def generate(clock: Clock): Unit = {
    impl(clock, implIO(ioType), methodArg(meth.inputType), methodRet(meth.outputType))
  }
}


case class StepAnnotation(target: ReferenceTarget, doFork: Boolean, isFinal: Boolean = false) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(target = n)
}