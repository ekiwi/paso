// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso
import chisel3._
import chisel3.experimental.{ChiselAnnotation, IO, annotate}
import firrtl.annotations.{ReferenceTarget, SingleTargetAnnotation}

import scala.collection.mutable

case class MethodGenerator(name: String, guard: Option[() => Bool], body: MethodBody) {
  def generate(): Unit = {
    assert(name.nonEmpty)
    body.generate(name + "_")
    val guard_cond = guard.map(_()).getOrElse(true.B)
    annotate(new ChiselAnnotation { override def toFirrtl = GuardAnnotation(guard_cond.toTarget) })
    guard_cond.suggestName("guard")
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
  def apply(): Unit = {}
}
case class IMethod[I <: Data](inputType: I, gen: MethodGenerator) {
  def apply(in: I): Unit = {}
}
case class OMethod[O <: Data](outputType: O, gen: MethodGenerator) {
  def apply(): O = { Wire(outputType) }
}
case class IOMethod[I <: Data, O <: Data](inputType: I, outputType: O, gen: MethodGenerator) {
  def apply(in: I): O = { Wire(outputType) }
}

trait MethodBody { def generate(prefix: String): Unit }
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
  override def generate(prefix: String): Unit = impl()
}
case class IMethodBody[I <: Data](inputType: I, impl: I => Unit) extends MethodBody with MethodBodyHelper {
  override def generate(prefix: String): Unit = impl(makeInput(inputType, prefix))
}
case class OMethodBody[O <: Data](outputType: O, impl: O => Unit) extends MethodBody with MethodBodyHelper {
  override def generate(prefix: String): Unit = impl(makeOutput(outputType, prefix))
}
case class IOMethodBody[I <: Data, O <: Data](inputType: I, outputType: O, impl: (I, O) => Unit) extends MethodBody with MethodBodyHelper {
  override def generate(prefix: String): Unit = impl(makeInput(inputType, prefix), makeOutput(outputType, prefix))
}

trait MethodParent { def addMethod(m: MethodGenerator): Unit }
case class NMethodBuilder(p: MethodParent, n: String, guard: Option[() => Bool] = None) {
  def in[I <: Data](inputType: I): IMethodBuilder[I] = IMethodBuilder(p, n, inputType, guard)
  def out[O <: Data](outputType: O): OMethodBuilder[O] = OMethodBuilder(p, n, outputType, guard)
  def when(cond: => Bool): NMethodBuilder = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: => Unit): NMethod = {
    val m = MethodGenerator(n, guard, NMethodBody(() => impl)) ; p.addMethod(m) ; NMethod(m)
  }
}
case class OMethodBuilder[O <: Data](p: MethodParent, n: String, outputType: O, guard: Option[() => Bool] = None) {
  def when(cond: => Bool): OMethodBuilder[O] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: O => Unit): OMethod[O] = {
    val m = MethodGenerator(n, guard, OMethodBody(outputType, impl)) ; p.addMethod(m)
    OMethod(outputType, m)
  }
}
case class IMethodBuilder[I <: Data](p: MethodParent, n : String, inputType: I, guard: Option[() => Bool] = None) {
  def out[O <: Data](outputType: O): IOMethodBuilder[I, O] = IOMethodBuilder(p, n, inputType, outputType, guard)
  def when(cond: => Bool): IMethodBuilder[I] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: I => Unit): IMethod[I] = {
    val m = MethodGenerator(n, guard, IMethodBody(inputType, impl)) ; p.addMethod(m)
    IMethod(inputType, m)
  }
}
case class IOMethodBuilder[I <: Data, O <: Data](p: MethodParent, n: String, inputType: I, outputType: O, guard: Option[() => Bool] = None) {
  def when(cond: => Bool): IOMethodBuilder[I,O] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: (I, O) => Unit): IOMethod[I,O] = {
    val m = MethodGenerator(n, guard, IOMethodBody(inputType, outputType, impl)) ; p.addMethod(m)
    IOMethod(inputType, outputType, m)
  }
}

class UntimedModule extends MultiIOModule with MethodParent {
  override def addMethod(m: MethodGenerator): Unit = methods.append(m)
  val methods = mutable.ArrayBuffer[MethodGenerator]()
  // TODO: automagically infer names like Chisel does for its native constructs
  def fun(name: String) = NMethodBuilder(this, name)
  //def fun[I <: Data](name: String)(inputs: I) = IMethodBuilder(this, name, inputs)
}

object UntimedModule {
  def apply[M <: UntimedModule](m: M): M = m
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