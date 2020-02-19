package chisel3.untimed // HACK in order to be able to access internal chisel methods!

import chisel3._
import chisel3.util._
import firrtl.ir

import scala.collection.mutable
import org.scalatest._

//class Method(val name: String, val inputs: Seq[Data], val outputs: Seq[Data]) {
//  val hasInput  = input.elements.nonEmpty
//  val hasOutput = output.elements.nonEmpty
//}

trait Method {
  def generate(): Unit
}

case class EmptyMethod(impl: () => Unit) extends Method {
  override def generate(): Unit = impl()
}
case class IMethod[I <: Data](inputType: I, impl: I => Unit) extends Method {
  override def generate(): Unit = impl(Wire(Input(inputType)).suggestName("inputs"))
}
case class OMethod[O <: Data](outputType: O, impl: O => Unit) extends Method {
  override def generate(): Unit = impl(Wire(Output(outputType)).suggestName("outputs"))
}
case class IOMethod[I <: Data, O <: Data](inputType: I, outputType: O, impl: (I, O) => Unit) extends Method {
  override def generate(): Unit = impl(Wire(Input(inputType)).suggestName("inputs"), Wire(Output(outputType)).suggestName("outputs"))
}

trait MethodParent { def addMethod(m: Method): Unit }
case class EmptyMethodBuilder(p: MethodParent, guard: Option[() => Bool] = None) {
  def out[O <: Data](outputType: O): OMethodBuilder[O] = OMethodBuilder(p, outputType, guard)
  def when(cond: => Bool): EmptyMethodBuilder = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: => Unit): Unit = p.addMethod(EmptyMethod(() => impl))
}
case class OMethodBuilder[O <: Data](p: MethodParent, outputType: O, guard: Option[() => Bool] = None) {
  def when(cond: => Bool): OMethodBuilder[O] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: O => Unit): Unit = p.addMethod(OMethod(outputType, impl))
}
case class IMethodBuilder[I <: Data](p: MethodParent, inputType: I, guard: Option[() => Bool] = None) {
  def out[O <: Data](outputType: O): IOMethodBuilder[I, O] = IOMethodBuilder(p, inputType, outputType, guard)
  def when(cond: => Bool): IMethodBuilder[I] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: I => Unit): Unit = p.addMethod(IMethod(inputType, impl))
}
case class IOMethodBuilder[I <: Data, O <: Data](p: MethodParent, inputType: I, outputType: O, guard: Option[() => Bool] = None) {
  def when(cond: => Bool): IOMethodBuilder[I,O] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: (I, O) => Unit): Unit = p.addMethod(IOMethod(inputType, outputType, impl))
}



class UntimedModule extends MultiIOModule with MethodParent {
//  def fun(inputs: => Unit) = ???
//  def fun(inputs: => Unit)(outputs: => Unit) = ???
//
//  def method(name: String)(foo: => Unit) = ???

  override def addMethod(m: Method): Unit = methods.append(m)
  val methods = mutable.ArrayBuffer[Method]()

  def fun = EmptyMethodBuilder(this)
  def fun[I <: Data](inputs: I) = IMethodBuilder(this, inputs)
    // foo foo should not be evaluated until the module is closed ...
    //foos.append(() => foo)
  //}
  //def fun[I <: Bundle, O <: Bundle](foo: (I, O) => Unit) = ???

}



class UntimedFifo[G <: Data](val depth: Int, dataType: G) extends UntimedModule {
  require(depth > 0)
  val mem = Mem(depth, dataType)
  val count = Reg(UInt((log2Ceil(depth) + 1).W))
  val read = Reg(UInt(log2Ceil(depth).W))
  val full = count === depth.U
  val empty = count === 0.U

  val push = fun(dataType).when(!full) { in =>
    mem.write(read + count, in)
    count := count + 1.U
  }

  val pop = fun.out(dataType).when(!empty) { out =>
    out := mem.read(read)
    count := count - 1.U
    read := read + 1.U
  }

  val push_pop = fun(dataType).out(dataType).when(!empty) { (in, out) =>
    mem.write(read + count, in)
    out := mem.read(read)
    read := read + 1.U
  }

  val idle = fun()
}



class FifoSpec extends FlatSpec {
  def elaborate(gen: () => RawModule): ir.Circuit = chisel3.aop.Aspect.getFirrtl(Driver.elaborate(gen))


  var m: Option[UntimedModule] = None
  val main = elaborate { () =>
    m = Some(new UntimedFifo(depth = 8, dataType = UInt(8.W)))
    m.get
  }

  val methods = m.get.methods.map { meth =>
    val c = elaborate(() => withClockAndReset(m.get.clock, m.get.reset) { new ModuleAspect(m.get) { meth.generate() } })
    c.modules.head.asInstanceOf[ir.Module].body
  }

  println(main.serialize)
  methods.zipWithIndex.foreach{case (m, ii) => println(s"Method #$ii") ; println(m.serialize) ; println()}
}
