// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso
import chisel3._
import chisel3.experimental.{ChiselAnnotation, IO, annotate}
import firrtl.annotations.{Annotation, ModuleTarget, ReferenceTarget, SingleTargetAnnotation}

import scala.collection.mutable

case class MethodGenerator(getParentName: () => String, name: String, guard: Option[() => Bool], body: MethodBody) {
  def generate(): Unit = {
    assert(name.nonEmpty)
    val guard_out = IO(Output(Bool())).suggestName(name + "_" + "guard")
    guard_out := guard.map(_()).getOrElse(true.B)
    annotate(new ChiselAnnotation { override def toFirrtl = GuardAnnotation(guard_out.toTarget) })
    val enabled_in = IO(Input(Bool())).suggestName(name + "_" + "enabled")
    body.generate(name + "_", enabled_in)
  }
}

case class GuardAnnotation(target: ReferenceTarget) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}
case class MethodIOAnnotation(target: ReferenceTarget, isInput: Boolean) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}

// TODO: rename to something more sensible
case class NMethod(gen: MethodGenerator) {
  def apply(): Unit = {
    throw new NotImplementedError("Calling methods with side effects is currently not supported!")
  }
}
case class IMethod[I <: Data](inputType: I, gen: MethodGenerator) {
  def apply(in: I): Unit = {
    throw new NotImplementedError("Calling methods with side effects is currently not supported!")
  }
}
class OMethodCallBundle[O <: Data](outputType: O) extends Bundle {
  val ret = Input(outputType)
  override def cloneType: this.type = {
    new OMethodCallBundle(outputType).asInstanceOf[this.type]
  }
}

case class OMethod[O <: Data](outputType: O, gen: MethodGenerator) {
  def apply(): O = {
    val name = gen.getParentName() + "." + gen.name
    val ii = MethodCall.getCallCount(name)
    // create port to emulate the function call
    val call = IO(new OMethodCallBundle(outputType)).suggestName(name + "_" + ii)
    annotate(new ChiselAnnotation { override def toFirrtl: Annotation = MethodCallAnnotation(call.ret.toTarget, name, ii, false) })
    call.ret
  }
}

class IOMethodCallBundle[I <: Data, O <: Data](inputType: I, outputType: O) extends Bundle {
  val arg = Output(inputType)
  val ret = Input(outputType)
  override def cloneType: this.type = {
    new IOMethodCallBundle(inputType, outputType).asInstanceOf[this.type]
  }
}

case class IOMethod[I <: Data, O <: Data](inputType: I, outputType: O, gen: MethodGenerator) {
  def apply(in: I): O = {
    val name = gen.getParentName() + "." + gen.name
    val ii = MethodCall.getCallCount(name)
    // create port to emulate the function call
    val call = IO(new IOMethodCallBundle(inputType, outputType)).suggestName(name + "_" + ii)
    annotate(new ChiselAnnotation { override def toFirrtl: Annotation = MethodCallAnnotation(call.arg.toTarget, name, ii, true) })
    annotate(new ChiselAnnotation { override def toFirrtl: Annotation = MethodCallAnnotation(call.ret.toTarget, name, ii, false) })
    call.arg := in
    call.ret
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

trait MethodBody { def generate(prefix: String, enabled: Bool): Unit }
trait MethodBodyHelper {
  protected def makeInput[T <: Data](t: T, prefix: String): T = {
    val i = IO(Input(t)).suggestName(prefix + "inputs")
    annotate(new ChiselAnnotation { override def toFirrtl = MethodIOAnnotation(i.toTarget, true) })
    i
  }
  protected def makeOutput[T <: Data](t: T, prefix: String): T = {
    val o = IO(Output(t)).suggestName(prefix + "outputs")
    annotate(new ChiselAnnotation { override def toFirrtl = MethodIOAnnotation(o.toTarget, false) })
    o
  }
}

case class NMethodBody(impl: () => Unit) extends MethodBody {
  override def generate(prefix: String, enabled: Bool): Unit = when(enabled) { impl() }
}
case class IMethodBody[I <: Data](inputType: I, impl: I => Unit) extends MethodBody with MethodBodyHelper {
  override def generate(prefix: String, enabled: Bool): Unit = {
    val in = makeInput(inputType, prefix)
    when(enabled) { impl(in) }
  }
}
case class OMethodBody[O <: Data](outputType: O, impl: O => Unit) extends MethodBody with MethodBodyHelper {
  override def generate(prefix: String, enabled: Bool): Unit = {
    val out = makeOutput(outputType, prefix)
    out := DontCare
    when(enabled) { impl(out) }
  }
}
case class IOMethodBody[I <: Data, O <: Data](inputType: I, outputType: O, impl: (I, O) => Unit) extends MethodBody with MethodBodyHelper {
  override def generate(prefix: String, enabled: Bool): Unit = {
    val in = makeInput(inputType, prefix)
    val out = makeOutput(outputType, prefix)
    out := DontCare
    when(enabled) { impl(in, out) }
  }
}

trait MethodParent { def addMethod(m: MethodGenerator): Unit; def getName: String }
case class NMethodBuilder(p: MethodParent, n: String, guard: Option[() => Bool] = None) {
  def in[I <: Data](inputType: I): IMethodBuilder[I] = IMethodBuilder(p, n, inputType, guard)
  def out[O <: Data](outputType: O): OMethodBuilder[O] = OMethodBuilder(p, n, outputType, guard)
  def when(cond: => Bool): NMethodBuilder = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: => Unit): NMethod = {
    val m = MethodGenerator(() => p.getName, n, guard, NMethodBody(() => impl)) ; p.addMethod(m) ; NMethod(m)
  }
}
case class OMethodBuilder[O <: Data](p: MethodParent, n: String, outputType: O, guard: Option[() => Bool] = None) {
  def when(cond: => Bool): OMethodBuilder[O] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: O => Unit): OMethod[O] = {
    val m = MethodGenerator(() => p.getName, n, guard, OMethodBody(outputType, impl)) ; p.addMethod(m)
    OMethod(outputType, m)
  }
}
case class IMethodBuilder[I <: Data](p: MethodParent, n : String, inputType: I, guard: Option[() => Bool] = None) {
  def out[O <: Data](outputType: O): IOMethodBuilder[I, O] = IOMethodBuilder(p, n, inputType, outputType, guard)
  def when(cond: => Bool): IMethodBuilder[I] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: I => Unit): IMethod[I] = {
    val m = MethodGenerator(() => p.getName, n, guard, IMethodBody(inputType, impl)) ; p.addMethod(m)
    IMethod(inputType, m)
  }
}
case class IOMethodBuilder[I <: Data, O <: Data](p: MethodParent, n: String, inputType: I, outputType: O, guard: Option[() => Bool] = None) {
  def when(cond: => Bool): IOMethodBuilder[I,O] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: (I, O) => Unit): IOMethod[I,O] = {
    val m = MethodGenerator(() => p.getName, n, guard, IOMethodBody(inputType, outputType, impl)) ; p.addMethod(m)
    IOMethod(inputType, outputType, m)
  }
}

class UntimedModule extends MultiIOModule with MethodParent {
  override def addMethod(m: MethodGenerator): Unit = methods.append(m)
  override def getName: String = this.pathName
  private val methods = mutable.ArrayBuffer[MethodGenerator]()
  def getMethods: Seq[MethodGenerator] = methods
  // TODO: automagically infer names like Chisel does for its native constructs
  def fun(name: String) = NMethodBuilder(this, name)
}

object UntimedModule {
  def apply[M <: UntimedModule](m: => M): M = {
    val sub = Module(m)
    annotate(new ChiselAnnotation { override def toFirrtl = SubmoduleAnnotation(sub.toTarget, sub) })
    sub
  }
}

case class SubmoduleAnnotation(target: ModuleTarget, untimed: UntimedModule) extends SingleTargetAnnotation[ModuleTarget] {
  def duplicate(n: ModuleTarget) = this.copy(n)
}


// TODO: inject spec finding through annotation
//case class PasoSpecAnnotation[M <: RawModule](target: ModuleTarget, spec: M => BindingBase)
//    extends SingleTargetAnnotation[ModuleTarget] {
//  override def duplicate(n: ModuleTarget): Annotation = this.copy(target = n)
//}
//
//// unfortunately only dotty (Scaly 3) supports trait parameters
//trait HasSpec extends RawModule {
//  val spec: BindingBase
//  annotate(new ChiselAnnotation with RunFirrtlTransform {
//    override def toFirrtl: Annotation = PasoSpecAnnotation(this.toNamed, spec)
//    override def transformClass = classOf[]
//  })
//}