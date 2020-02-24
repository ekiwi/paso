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

trait Protocol { def generate(): Unit }
case class NProtocol[IO <: Data](ioType: IO, meth: NMethod, impl: IO => Unit) extends Protocol {
  override def generate(): Unit = {
    impl(Wire(Input(ioType)).suggestName("io"))
  }
}
case class IProtocol[IO <: Data, I <: Data](ioType: IO, meth: IMethod[I], impl: (IO, I) => Unit) extends Protocol {
  override def generate(): Unit = {
    impl(Wire(Input(ioType)).suggestName("io"), Wire(Output(meth.inputType)).suggestName("inputs"))
  }
}
case class OProtocol[IO <: Data, O <: Data](ioType: IO, meth: OMethod[O], impl: (IO, O) => Unit) extends Protocol {
  override def generate(): Unit = {
    impl(Wire(Input(ioType)).suggestName("io"), Wire(Input(meth.outputType)).suggestName("outputs"))
  }
}
case class IOProtocol[IO <: Data, I <: Data, O <: Data](ioType: IO, meth: IOMethod[I,O], impl: (IO, I, O) => Unit) extends Protocol {
  override def generate(): Unit = {
    impl(Wire(Input(ioType)).suggestName("io"), Wire(Output(meth.inputType)).suggestName("inputs"),
      Wire(Input(meth.outputType)).suggestName("outputs"))
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

  implicit class testableData[T <: Data](x: T) {
    def poke(value: T) = println(s"$x <- $value")
    def expect(value: T) = println(s"$x == $value ?")
  }

  val invs = new mutable.ArrayBuffer[IM => Unit]()
  def invariances(gen: IM => Unit): Unit = invs.append(gen)

  implicit def memToVec[T <: Data](m: Mem[T]): Vec[T] = Vec(m.length.toInt, m.t).suggestName(m.pathName)


  val maps = new mutable.ArrayBuffer[(IM,SM) => Unit]()
  def mapping(gen: (IM, SM) => Unit): Unit = maps.append(gen)

  def step(): Unit =  println(s"STEP")
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

class SpecBinding(impl: CircularPointerFifo, spec: UntimedFifo[UInt]) extends Binding(impl, spec) {
  // TODO: instantiate spec based on impl parametrization
  require(impl.width == spec.dataType.getWidth)
  require(impl.depth == spec.depth)

  // alternative which might be nicer as it would allow us to keep all of spec constant
  protocol(spec.push)(impl.io) { (dut, in) =>
    dut.pop.poke(false.B)
    dut.push.poke(true.B)
    dut.data_in.poke(in)
    dut.full.expect(false.B)
    step()
  }

  protocol(spec.pop)(impl.io) { (dut, out) =>
    dut.pop.poke(true.B)
    dut.push.poke(false.B)
    dut.data_out.expect(out)
    dut.empty.expect(false.B)
    step()
  }

  protocol(spec.push_pop)(impl.io) { (dut, in, out) =>
    dut.pop.poke(true.B)
    dut.push.poke(true.B)
    dut.data_in.poke(in)
    dut.data_out.expect(out)
    dut.empty.expect(false.B)
    step()
  }

  protocol(spec.idle)(impl.io) { dut =>
    dut.pop.poke(false.B)
    dut.push.poke(false.B)
    step()
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
  val depth = 8
  val width = 8

  // Driver.execute(Array("--compiler", "mverilog"), () => new CircularPointerFifo(32, 32))

  def elaborate(gen: () => RawModule): ir.Circuit = chisel3.aop.Aspect.getFirrtl(Driver.elaborate(gen))

  def elaborateBody(m: RawModule, gen: () => Unit): ir.Statement =
    elaborateInContextOfModule(m, gen).modules.head.asInstanceOf[ir.Module].body

  var m: Option[UntimedFifo[UInt]] = None
  val main = elaborate { () =>
    m = Some(new UntimedFifo(depth = depth, dataType = UInt(width.W)))
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

  var impl: Option[CircularPointerFifo] = None
  val impl_fir = elaborate{() => impl = Some(new CircularPointerFifo(depth = depth, width = width) ); impl.get}

  println("Implementation:")
  println(impl_fir.serialize)

  println("Binding...")
  val binding = new SpecBinding(impl.get, m.get)

  // try to elaborate thing in the binding
  def elaborate_protocol(p: Protocol) = {
    p.generate()
  }

  binding.protos.foreach{ p => elaborate_protocol(p) }


}
