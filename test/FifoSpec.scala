import chisel3._
import chisel3.util._
import firrtl.ir
import chisel3.hacks.elaborateInContextOfModule

import scala.collection.mutable
import org.scalatest._

trait MethodGenerator {
  def generate(): Unit
}

case class EmptyMethodGenerator(impl: () => Unit) extends MethodGenerator {
  override def generate(): Unit = impl()
}
case class IMethodGenerator[I <: Data](inputType: I, impl: I => Unit) extends MethodGenerator {
  override def generate(): Unit = impl(Wire(Input(inputType)).suggestName("inputs"))
}
case class OMethodGenerator[O <: Data](outputType: O, impl: O => Unit) extends MethodGenerator {
  override def generate(): Unit = impl(Wire(Output(outputType)).suggestName("outputs"))
}
case class IOMethodGenerator[I <: Data, O <: Data](inputType: I, outputType: O, impl: (I, O) => Unit) extends MethodGenerator {
  override def generate(): Unit = impl(Wire(Input(inputType)).suggestName("inputs"), Wire(Output(outputType)).suggestName("outputs"))
}

trait MethodParent { def addMethod(m: MethodGenerator): Unit }
case class EmptyMethodBuilder(p: MethodParent, guard: Option[() => Bool] = None) {
  def out[O <: Data](outputType: O): OMethodBuilder[O] = OMethodBuilder(p, outputType, guard)
  def when(cond: => Bool): EmptyMethodBuilder = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: => Unit): Unit = p.addMethod(EmptyMethodGenerator(() => impl))
}
case class OMethodBuilder[O <: Data](p: MethodParent, outputType: O, guard: Option[() => Bool] = None) {
  def when(cond: => Bool): OMethodBuilder[O] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: O => Unit): Unit = p.addMethod(OMethodGenerator(outputType, impl))
}
case class IMethodBuilder[I <: Data](p: MethodParent, inputType: I, guard: Option[() => Bool] = None) {
  def out[O <: Data](outputType: O): IOMethodBuilder[I, O] = IOMethodBuilder(p, inputType, outputType, guard)
  def when(cond: => Bool): IMethodBuilder[I] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: I => Unit): Unit = p.addMethod(IMethodGenerator(inputType, impl))
}
case class IOMethodBuilder[I <: Data, O <: Data](p: MethodParent, inputType: I, outputType: O, guard: Option[() => Bool] = None) {
  def when(cond: => Bool): IOMethodBuilder[I,O] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: (I, O) => Unit): Unit = p.addMethod(IOMethodGenerator(inputType, outputType, impl))
}

class UntimedModule extends MultiIOModule with MethodParent {
  override def addMethod(m: MethodGenerator): Unit = methods.append(m)
  val methods = mutable.ArrayBuffer[MethodGenerator]()
  def fun = EmptyMethodBuilder(this)
  def fun[I <: Data](inputs: I) = IMethodBuilder(this, inputs)
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class FifoSpec extends FlatSpec {
  def elaborate(gen: () => RawModule): ir.Circuit = chisel3.aop.Aspect.getFirrtl(Driver.elaborate(gen))


  var m: Option[UntimedModule] = None
  val main = elaborate { () =>
    m = Some(new UntimedFifo(depth = 8, dataType = UInt(8.W)))
    m.get
  }

  val methods = m.get.methods.map { meth =>
    val c: ir.Circuit = elaborateInContextOfModule(m.get, meth.generate)
    c.modules.head.asInstanceOf[ir.Module].body
  }

  println(main.serialize)
  methods.zipWithIndex.foreach{case (m, ii) => println(s"Method #$ii") ; println(m.serialize) ; println()}
}
