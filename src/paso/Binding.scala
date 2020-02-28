// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>
package paso

import chisel3._
import chisel3.experimental.{ChiselAnnotation, IO, annotate}
import firrtl.annotations.{ReferenceTarget, SingleTargetAnnotation}

import scala.collection.mutable


trait Protocol {
  def methodName: String
  def generate(): Unit
}
case class NProtocol[IO <: Data](ioType: IO, meth: NMethod, impl: IO => Unit) extends Protocol {
  override def methodName = meth.gen.name
  override def generate(): Unit = {
    impl(IO(Flipped(ioType)).suggestName("io"))
  }
}
case class IProtocol[IO <: Data, I <: Data](ioType: IO, meth: IMethod[I], impl: (IO, I) => Unit) extends Protocol {
  override def methodName = meth.gen.name
  override def generate(): Unit = {
    impl(IO(Flipped(ioType)).suggestName("io"), IO(Input(meth.inputType)).suggestName("inputs"))
    //impl(Input(ioType).suggestName("io"), Output(meth.inputType).suggestName("inputs"))
  }
}
case class OProtocol[IO <: Data, O <: Data](ioType: IO, meth: OMethod[O], impl: (IO, O) => Unit) extends Protocol {
  override def methodName = meth.gen.name
  override def generate(): Unit = {
    impl(IO(Flipped(ioType)).suggestName("io"), IO(Output(meth.outputType)).suggestName("outputs"))
  }
}
case class IOProtocol[IO <: Data, I <: Data, O <: Data](ioType: IO, meth: IOMethod[I,O], impl: (IO, I, O) => Unit) extends Protocol {
  override def methodName = meth.gen.name
  override def generate(): Unit = {
    impl(IO(Flipped(ioType)).suggestName("io"), IO(Input(meth.inputType)).suggestName("inputs"),
      IO(Output(meth.outputType)).suggestName("outputs"))
  }
}



class Binding[IM <: RawModule, SM <: UntimedModule](impl: IM, spec: SM) {
  val protos = new mutable.ArrayBuffer[Protocol]()
  def protocol[IO <: Data](meth: NMethod)(io: IO)(gen: IO => Unit): Unit =
    protos.append(NProtocol(chiselTypeOf(io), meth, gen))
  def protocol[O <: Data, IO <: Data](meth: OMethod[O])(io: IO)(gen: (IO, O) => Unit): Unit =
    protos.append(OProtocol(chiselTypeOf(io), meth, gen))
  def protocol[I <: Data, IO <: Data](meth: IMethod[I])(io: IO)(gen: (IO, I) => Unit): Unit =
    protos.append(IProtocol(chiselTypeOf(io), meth, gen))
  def protocol[I <: Data, O <: Data, IO <: Data](meth: IOMethod[I, O])(io: IO)(gen: (IO, I,O) => Unit): Unit =
    protos.append(IOProtocol(chiselTypeOf(io), meth, gen))

  // replace default chisel assert
  def assert(cond: => Bool): Unit = {
    val w = Wire(Bool()).suggestName("assert")
    w := cond
    annotate(new ChiselAnnotation { override def toFirrtl = AssertAnnotation(w.toTarget) })
  }


  // TODO: support more than just UInt
  implicit class testableData[T <: UInt](x: T) {
    def poke(value: T): Unit = {
      x := value
    }
    def expect(value: T): Unit = {
      val w = Wire(Bool()).suggestName("expect")
      w := x === value
      annotate(new ChiselAnnotation { override def toFirrtl = ExpectAnnotation(w.toTarget) })
    }
  }

  val invs = new mutable.ArrayBuffer[IM => Unit]()
  def invariances(gen: IM => Unit): Unit = invs.append(gen)

  implicit def memToVec[T <: Data](m: Mem[T]): Vec[T] = {
    Wire(Vec(m.length.toInt, m.t)).suggestName(m.pathName.replace('.', '_'))
  }


  val maps = new mutable.ArrayBuffer[(IM,SM) => Unit]()
  def mapping(gen: (IM, SM) => Unit): Unit = maps.append(gen)

  def step(): Unit = {
    val w = Wire(Bool()).suggestName("step")
    annotate(new ChiselAnnotation { override def toFirrtl = StepAnnotation(w.toTarget) })
  }

  implicit class comparableVec[T <: UInt](x: Vec[T]) {
    def ===(y: Vec[T]): Bool = {
      require(x.length > 0)
      require(x.length == y.length)
      x.zip(y).map{ case (a, b) => a === b}.reduceLeft[Bool]{ case (a,b) => a && b }
    }
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