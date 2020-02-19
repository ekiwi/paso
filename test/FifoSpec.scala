import chisel3._
import chisel3.util._
import firrtl.ir
import chisel3.hacks.elaborateInContextOfModule

import scala.collection.mutable
import org.scalatest._


case class MethodGenerator(name: String, guard: Option[() => Bool], body: MethodBody)


trait MethodBody { def generate(): Unit }
case class EmptyMethodBody(impl: () => Unit) extends MethodBody {
  override def generate(): Unit = impl()
}
case class IMethodBody[I <: Data](inputType: I, impl: I => Unit) extends MethodBody {
  override def generate(): Unit = impl(Wire(Input(inputType)).suggestName("inputs"))
}
case class OMethodBody[O <: Data](outputType: O, impl: O => Unit) extends MethodBody {
  override def generate(): Unit = impl(Wire(Output(outputType)).suggestName("outputs"))
}
case class IOMethodBody[I <: Data, O <: Data](inputType: I, outputType: O, impl: (I, O) => Unit) extends MethodBody {
  override def generate(): Unit = impl(Wire(Input(inputType)).suggestName("inputs"), Wire(Output(outputType)).suggestName("outputs"))
}

trait MethodParent { def addMethod(m: MethodGenerator): Unit }
case class EmptyMethodBuilder(p: MethodParent, n: String, guard: Option[() => Bool] = None) {
  def in[I <: Data](inputType: I): IMethodBuilder[I] = IMethodBuilder(p, n, inputType, guard)
  def out[O <: Data](outputType: O): OMethodBuilder[O] = OMethodBuilder(p, n, outputType, guard)
  def when(cond: => Bool): EmptyMethodBuilder = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: => Unit): MethodGenerator = {val m = MethodGenerator(n, guard, EmptyMethodBody(() => impl)) ; p.addMethod(m) ; m}
}
case class OMethodBuilder[O <: Data](p: MethodParent, n: String, outputType: O, guard: Option[() => Bool] = None) {
  def when(cond: => Bool): OMethodBuilder[O] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: O => Unit): MethodGenerator = {
    val m = MethodGenerator(n, guard, OMethodBody(outputType, impl)) ; p.addMethod(m) ; m
  }
}
case class IMethodBuilder[I <: Data](p: MethodParent, n : String, inputType: I, guard: Option[() => Bool] = None) {
  def out[O <: Data](outputType: O): IOMethodBuilder[I, O] = IOMethodBuilder(p, n, inputType, outputType, guard)
  def when(cond: => Bool): IMethodBuilder[I] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: I => Unit): MethodGenerator = {
    val m = MethodGenerator(n, guard, IMethodBody(inputType, impl)) ; p.addMethod(m) ; m
  }
}
case class IOMethodBuilder[I <: Data, O <: Data](p: MethodParent, n: String, inputType: I, outputType: O, guard: Option[() => Bool] = None) {
  def when(cond: => Bool): IOMethodBuilder[I,O] = { require(guard.isEmpty) ; this.copy(guard = Some(() => cond))}
  def apply(impl: (I, O) => Unit): MethodGenerator = {
    val m = MethodGenerator(n, guard, IOMethodBody(inputType, outputType, impl)) ; p.addMethod(m) ; m
  }
}

class UntimedModule extends MultiIOModule with MethodParent {
  override def addMethod(m: MethodGenerator): Unit = methods.append(m)
  val methods = mutable.ArrayBuffer[MethodGenerator]()
  // TODO: automagically infer names like Chisel does for its native constructs
  def fun(name: String) = EmptyMethodBuilder(this, name)
  //def fun[I <: Data](name: String)(inputs: I) = IMethodBuilder(this, name, inputs)
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class UntimedFifo[G <: Data](val depth: Int, dataType: G) extends UntimedModule {
  require(depth > 0)
  val mem = Mem(depth, dataType)
  val count = Reg(UInt((log2Ceil(depth) + 1).W))
  val read = Reg(UInt(log2Ceil(depth).W))
  val full = count === depth.U
  val empty = count === 0.U

  val push = fun("push").in(dataType).when(!full) { in =>
    mem.write(read + count, in)
    count := count + 1.U
  }

  val pop = fun("pop").out(dataType).when(!empty) { out =>
    out := mem.read(read)
    count := count - 1.U
    read := read + 1.U
  }

  val push_pop = fun("push_pop").in(dataType).out(dataType).when(!empty) { (in, out) =>
    mem.write(read + count, in)
    out := mem.read(read)
    read := read + 1.U
  }

  val idle = fun("idle")() // TODO: closing brackets are unfortunatelly required for method to be registered for now :(
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class FifoSpec extends FlatSpec {
  def elaborate(gen: () => RawModule): ir.Circuit = chisel3.aop.Aspect.getFirrtl(Driver.elaborate(gen))

  def elaborateBody(m: RawModule, gen: () => Unit): ir.Statement =
    elaborateInContextOfModule(m, gen).modules.head.asInstanceOf[ir.Module].body

  var m: Option[UntimedModule] = None
  val main = elaborate { () =>
    m = Some(new UntimedFifo(depth = 8, dataType = UInt(8.W)))
    m.get
  }

  val methods = m.get.methods.map { meth =>
    val body = elaborateBody(m.get, meth.body.generate)
    val guard =  meth.guard.map(g => elaborateBody(m.get, () => { val guard = g() }))
    (meth.name, guard, body)
  }

  println(main.serialize)
  methods.foreach{ case (name, guard, body) =>
    println(s"Method $name")
    guard.foreach{g => println(s"guard: ${g.serialize}")}
    println(body.serialize)
    println()}
}
