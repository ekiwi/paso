// Copyright 2020 The Regents of the University of California
// Copyright 2020, SiFive, Inc
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.untimed

import chisel3._
import chisel3.experimental.{ChiselAnnotation, IO, annotate}
import firrtl.annotations.{Annotation, InstanceTarget, IsModule, ModuleTarget, MultiTargetAnnotation, ReferenceTarget, SingleTargetAnnotation, Target}

import scala.collection.mutable

private[paso] trait MethodParent {
  private[paso] def addMethod(m: Method): Unit
  private[paso] def toTarget: ModuleTarget
  private[paso] def toAbsoluteTarget: IsModule
  private[paso] def isElaborated: Boolean
}

trait Method {
  def name: String
  private[paso ]def guard: () => Bool
  private[paso] def generate(): Unit
}

case class NMethod(name: String, guard: () => Bool, impl: () => Unit, parent: MethodParent) extends Method {
  def apply(): Unit = {
    require(!parent.isElaborated, "TODO: implement method calls for elaborated UntimedMoudles")
    throw new NotImplementedError("Calling methods with side effects is currently not supported!")
  }
  override private[paso] def generate(): Unit = {
    val io = IO(new MethodIO(UInt(0.W), UInt(0.W))).suggestName(name)
    annotate(new ChiselAnnotation { override def toFirrtl = MethodIOAnnotation(io.toTarget, name) })
    when(io.enabled) { impl() }
    io.guard := guard()
  }
}

case class IMethod[I <: Data](name: String, guard: () => Bool, inputType: I, impl: I => Unit, parent: MethodParent) extends Method {
  def apply(in: I): Unit = {
    require(!parent.isElaborated, "TODO: implement method calls for elaborated UntimedMoudles")
    throw new NotImplementedError("Calling methods with side effects is currently not supported!")
  }
  override private[paso] def generate(): Unit = {
    val io = IO(new MethodIO(inputType, UInt(0.W))).suggestName(name)
    annotate(new ChiselAnnotation { override def toFirrtl = MethodIOAnnotation(io.toTarget, name) })
    when(io.enabled) { impl(io.arg) }
    io.guard := guard()
  }
}

case class OMethod[O <: Data](name: String, guard: () => Bool, outputType: O, impl: O => Unit, parent: MethodParent) extends Method {
  def apply(): O = {
    require(!parent.isElaborated, "TODO: implement method calls for elaborated UntimedModules")
    val ii = MethodCall.getCallCount(name)
    // create port to emulate the function call
    val call = IO(new MethodCallIO(UInt(0.W), outputType)).suggestName(name + "_call_" + ii)
    annotate(new ChiselAnnotation { override def toFirrtl: Annotation = MethodCallAnnotation(call.toTarget, parent.toAbsoluteTarget, name) })
    call.enabled := true.B
    call.ret
  }
  override private[paso] def generate(): Unit = {
    val io = IO(new MethodIO(UInt(0.W), outputType)).suggestName(name)
    annotate(new ChiselAnnotation { override def toFirrtl = MethodIOAnnotation(io.toTarget, name) })
    io.ret := DontCare
    when(io.enabled) { impl(io.ret) }
    io.guard := guard()
  }
}

case class IOMethod[I <: Data, O <: Data](name: String, guard: () => Bool, inputType: I, outputType: O, impl: (I,O) => Unit, parent: MethodParent) extends Method {
  def apply(in: I): O = {
    require(!parent.isElaborated, "TODO: implement method calls for elaborated UntimedModules")
    val ii = MethodCall.getCallCount(name)
    // create port to emulate the function call
    val call = IO(new MethodCallIO(inputType, outputType)).suggestName(name + "_call_" + ii)
    annotate(new ChiselAnnotation { override def toFirrtl: Annotation = MethodCallAnnotation(call.toTarget, parent.toTarget, name) })
    call.arg := in
    call.enabled := true.B
    call.ret
  }
  override private[paso] def generate(): Unit = {
    val io = IO(new MethodIO(inputType, outputType)).suggestName(name)
    annotate(new ChiselAnnotation { override def toFirrtl = MethodIOAnnotation(io.toTarget, name) })
    io.ret := DontCare
    when(io.enabled) { impl(io.arg, io.ret) }
    io.guard := guard()
  }
}

// TODO: MethodCallIO is essentially just a flipped MethodIO
class MethodCallIO[I <: Data, O <: Data](inputType: I, outputType: O) extends Bundle {
  val arg = Output(inputType)  // inputs to the method, only valid if enabled is true
  val ret = Input(outputType)  // outputs of the method, only valid if enabled is true
  val enabled = Output(Bool()) // will be true if the method is called
  val guard = Input(Bool())
  override def cloneType: this.type = {
    new MethodCallIO(inputType, outputType).asInstanceOf[this.type]
  }
}
class MethodIO[I <: Data, O <: Data](inputType: I, outputType: O) extends Bundle {
  val enabled = Input(Bool()) // may only be asserted if guard is true
  val guard = Output(Bool())  // indicated whether the method can be executed
  val arg = Input(inputType)
  val ret = Output(outputType)
  override def cloneType: this.type = {
    new MethodIO(inputType, outputType).asInstanceOf[this.type]
  }
}

// singleton to ensure that all call sites get unique names (this is a bit ugly and not thread-safe :( )
object MethodCall {
  private val callSiteCount = mutable.HashMap[String, Int]()
  def getCallCount(name: String): Int = {
    val old = callSiteCount.getOrElse(name, -1)
    val next = old + 1
    callSiteCount(name) = next
    next
  }
}

case class MethodIOAnnotation(target: ReferenceTarget, name: String) extends SingleTargetAnnotation[ReferenceTarget] {
  override def duplicate(n: ReferenceTarget): MethodIOAnnotation = copy(target = n)
}

case class MethodCallAnnotation(callIO: ReferenceTarget, calleeParent: IsModule, calleeName: String) extends MultiTargetAnnotation {
  override val targets = List(List(callIO), List(calleeParent))

  override def duplicate(n: Seq[Seq[Target]]): MethodCallAnnotation = {
    assert(n.length == 2, "Need signal + parent")
    assert(n(1).length == 1, "Method parent should always stay a single InstanceTarget!")
    assert(n.head.length == 1, "Call signal should not be split up. Make sure to remove this annotation before running LowerTypes!")
    copy(callIO = n.head.head.asInstanceOf[ReferenceTarget], calleeParent = n(1).head.asInstanceOf[IsModule])
  }
}