import chisel3._
import chisel3.util._
import firrtl.ir
import chisel3.hacks.elaborateInContextOfModule

import scala.collection.mutable
import org.scalatest._


case class MethodGenerator(name: String, guard: Option[() => Bool], body: MethodBody)

// TODO: rename to something more sensible
case class NMethod(gen: MethodGenerator)
case class IMethod[I <: Data](inputType: I, gen: MethodGenerator)
case class OMethod[O <: Data](outputType: O, gen: MethodGenerator)
case class IOMethod[I <: Data, O <: Data](inputType: I, outputType: O, gen: MethodGenerator)

trait MethodBody { def generate(): Unit }
case class NMethodBody(impl: () => Unit) extends MethodBody {
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

class Binding[IM <: RawModule, SM <: UntimedModule](impl: IM, spec: SM) {
  def protocol[IO <: Data](meth: NMethod)(io: IO)(gen: IO => Unit) = ???
  def protocol[O <: Data, IO <: Data](meth: OMethod[O])(io: IO)(gen: (IO, O) => Unit) = ???
  def protocol[I <: Data, IO <: Data](meth: IMethod[I])(io: IO)(gen: (IO, I) => Unit) = ???
  def protocol[I <: Data, O <: Data, IO <: Data](meth: IOMethod[I, O])(io: IO)(gen: (IO, I,O) => Unit) = ???

  implicit class testableData[T <: Data](x: T) {
    def poke(value: T) = println(s"$x <- $value")
  }

  def invariances(gen: IM => Unit) = ???

  implicit def memToVec[T <: Data](m: Mem[T]): Vec[T] = Vec(m.length.toInt, m.t)

  def mapping(gen: (IM, SM) => Unit) = ???
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class UntimedFifo[G <: Data](val depth: Int, val dataType: G) extends UntimedModule {
  require(depth > 0)
  require(isPow2(depth))
  val mem = Reg(Vec(depth, dataType))
  val count = Reg(UInt((log2Ceil(depth) + 1).W))
  val read = Reg(UInt(log2Ceil(depth).W))
  val full = count === depth.U
  val empty = count === 0.U

  val push = fun("push").in(dataType).when(!full) { in =>
    mem(read + count) := in
    count := count + 1.U
  }

  val pop = fun("pop").out(dataType).when(!empty) { out =>
    out := mem(read)
    count := count - 1.U
    read := read + 1.U
  }

  val push_pop = fun("push_pop").in(dataType).out(dataType).when(!empty) { (in, out) =>
    mem(read + count) :=  in
    out := mem(read)
    read := read + 1.U
  }

  val idle = fun("idle")() // TODO: closing brackets are unfortunatelly required for method to be registered for now :(
}

// rewrite of Makai Mann's circular fifo in Chisel
class CircularPointerFifo(val width: Int, val depth: Int, fixed: Boolean = false) extends Module {
  require(isPow2(depth))
  val io = IO(new Bundle{
    val push = Input(Bool())
    val pop = Input(Bool())
    val data_in = Input(UInt(width.W))
    val full = Output(Bool())
    val empty = Output(Bool())
    val data_out = Output(UInt(width.W))
  })

  val counter_init = 0.U((log2Ceil(depth) + 1).W)

  val cnt = RegInit(counter_init)
  cnt := cnt + io.push - io.pop

  val pointer_width = if(fixed) log2Ceil(depth) else log2Ceil(depth) + 1
  val pointer_init = 0.U(pointer_width.W)

  val wrPtr = RegInit(pointer_init)
  wrPtr := wrPtr + io.push

  val rdPtr = RegInit(pointer_init)
  rdPtr := rdPtr + io.pop

  io.empty := cnt === 0.U
  io.full := cnt === depth.U

  val entries = Mem(depth, UInt(width.W))
  val input_data = Mux(io.push, io.data_in, entries.read(wrPtr))
  entries.write(wrPtr, input_data)

  io.data_out := entries.read(rdPtr)
}

class SpecBinding(impl: CircularPointerFifo, spec: UntimedFifo[UInt]) extends Binding(impl, spec) {
  // TODO: instantiate spec based on impl parametrization
  require(impl.width == spec.dataType.getWidth)
  require(impl.depth == spec.depth)

  // alternative which might be nicer as it would allow us to keep all of spec constant
  protocol(spec.push)(impl.io) { (dut, in) =>
    // TODO
  }

  protocol(spec.pop)(impl.io) { (dut, out) =>
    // TODO
  }

  protocol(spec.push_pop)(impl.io) { (dut, in, out) =>
    // TODO
  }

  protocol(spec.idle)(impl.io) { dut =>
    dut.pop.poke(false.B)
    dut.push.poke(false.B)
  }

  mapping { (impl, spec) =>
    spec.count <> impl.cnt
    spec.read <> impl.rdPtr
    spec.mem <> impl.entries
  }

  invariances { dut =>
    assert(dut.cnt <= dut.depth.U)
    assert(dut.rdPtr < dut.depth.U)
    assert(dut.wrPtr < dut.depth.U)
    when(dut.cnt === 0.U) {
      assert(dut.wrPtr === dut.rdPtr)
    } .elsewhen(dut.wrPtr > dut.rdPtr) {
      assert(dut.cnt === dut.wrPtr - dut.rdPtr)
    } .otherwise {
      assert(dut.cnt === dut.depth.U + dut.wrPtr - dut.rdPtr)
    }
  }
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class FifoSpec extends FlatSpec {
  // Driver.execute(Array("--compiler", "mverilog"), () => new CircularPointerFifo(32, 32))

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
