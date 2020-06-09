// Copyright 2020 The Regents of the University of California
// Copyright 2020, SiFive, Inc
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.untimed

import chisel3._
import chisel3.experimental.{ChiselAnnotation, IO, annotate}
import firrtl.annotations.{Annotation, ReferenceTarget, SingleTargetAnnotation}

import scala.collection.mutable

private[paso] trait MethodParent {
  private[paso] def addMethod(m: Method): Unit
  private[paso] def getName: String
  private[paso] def isElaborated: Boolean
}

trait Method {
  def name: String
  def guard: () => Bool
  //def getParentName: String
  private[paso] def generate(): Unit = {
    assert(name.nonEmpty)
    val guard_out = IO(Output(Bool())).suggestName(name + "_" + "guard")
    guard_out := guard()
    val enabled_in = IO(Input(Bool())).suggestName(name + "_" + "enabled")
    generateBody(enabled_in)
  }
  def makeInput[T <: Data](t: T): T = {
    IO(Input(t)).suggestName(name + "_inputs")
  }
  def makeOutput[T <: Data](t: T): T = {
    IO(Output(t)).suggestName(name + "_outputs")
  }
  protected def generateBody(enabled: Bool): Unit
}

case class NMethod(name: String, guard: () => Bool, impl: () => Unit, parent: MethodParent) extends Method {
  def apply(): Unit = {
    require(!parent.isElaborated, "TODO: implement method calls for elaborated UntimedMoudles")
    throw new NotImplementedError("Calling methods with side effects is currently not supported!")
  }
  override protected def generateBody(enabled: Bool): Unit = when(enabled) { impl() }
}

case class IMethod[I <: Data](name: String, guard: () => Bool, inputType: I, impl: I => Unit, parent: MethodParent) extends Method {
  def apply(in: I): Unit = {
    require(!parent.isElaborated, "TODO: implement method calls for elaborated UntimedMoudles")
    throw new NotImplementedError("Calling methods with side effects is currently not supported!")
  }
  override def generateBody(enabled: Bool): Unit = {
    val in = makeInput(inputType)
    when(enabled) { impl(in) }
  }
}

case class OMethod[O <: Data](name: String, guard: () => Bool, outputType: O, impl: O => Unit, parent: MethodParent) extends Method {
  def apply(): O = {
    require(!parent.isElaborated, "TODO: implement method calls for elaborated UntimedMoudles")
    val fullName = parent.getName + "." + name
    val ii = MethodCall.getCallCount(fullName)
    // create port to emulate the function call
    val call = IO(new OMethodCallBundle(outputType)).suggestName(fullName + "_" + ii)
    annotate(new ChiselAnnotation { override def toFirrtl: Annotation = MethodCallAnnotation(call.ret.toTarget, fullName, ii, false) })
    call.ret
  }
  override def generateBody(enabled: Bool): Unit = {
    val out = makeOutput(outputType)
    out := DontCare
    when(enabled) { impl(out) }
  }
}

case class IOMethod[I <: Data, O <: Data](name: String, guard: () => Bool, inputType: I, outputType: O, impl: (I,O) => Unit, parent: MethodParent) extends Method {
  def apply(in: I): O = {
    require(!parent.isElaborated, "TODO: implement method calls for elaborated UntimedMoudles")
    val fullName = parent.getName + "." + name
    val ii = MethodCall.getCallCount(fullName)
    // create port to emulate the function call
    val call = IO(new IOMethodCallBundle(inputType, outputType)).suggestName(fullName + "_" + ii)
    annotate(new ChiselAnnotation { override def toFirrtl: Annotation = MethodCallAnnotation(call.arg.toTarget, fullName, ii, true) })
    annotate(new ChiselAnnotation { override def toFirrtl: Annotation = MethodCallAnnotation(call.ret.toTarget, fullName, ii, false) })
    call.arg := in
    call.ret
  }
  override def generateBody(enabled: Bool): Unit = {
    val in = makeInput(inputType)
    val out = makeOutput(outputType)
    out := DontCare
    when(enabled) { impl(in, out) }
  }
}


class OMethodCallBundle[O <: Data](outputType: O) extends Bundle {
  val ret = Input(outputType)
  override def cloneType: this.type = {
    new OMethodCallBundle(outputType).asInstanceOf[this.type]
  }
}
class IOMethodCallBundle[I <: Data, O <: Data](inputType: I, outputType: O) extends Bundle {
  val arg = Output(inputType)
  val ret = Input(outputType)
  override def cloneType: this.type = {
    new IOMethodCallBundle(inputType, outputType).asInstanceOf[this.type]
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

case class MethodCallAnnotation(target: ReferenceTarget, name: String, ii: Int, isArg: Boolean) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}