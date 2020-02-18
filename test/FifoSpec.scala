import chisel3._
import chisel3.util._

import org.scalatest._

class Method[I <: Bundle, O <: Bundle](val name: String, val input: I, val output: O) {
  val hasInput  = input.elements.nonEmpty
  val hasOutput = output.elements.nonEmpty
}


class UntimedModule extends MultiIOModule {
//  def fun(inputs: => Unit) = ???
//  def fun(inputs: => Unit)(outputs: => Unit) = ???
//
//  def method(name: String)(foo: => Unit) = ???

  def fun() = {}
  def fun(foo: => Unit) = {
    foo
  }
  //def fun[I <: Bundle, O <: Bundle](foo: (I, O) => Unit) = ???

}



class UntimedFifo[G <: Data](val depth: Int, dataType: G) extends UntimedModule {
  require(depth > 0)
  val mem = Mem(depth, dataType)
  val count = Reg(UInt((log2Ceil(depth) + 1).W))
  val read = Reg(UInt(log2Ceil(depth).W))
  val full = count === depth.U
  val empty = count === 0.U

  val push = fun {
    val in = IO(Input(dataType))
    mem.write(read + count, in)
    count := count + 1.U
  }

  val pop = fun {
    val out = IO(Output(dataType))
    out := mem.read(read)
    count := count - 1.U
    read := read + 1.U
  }

  val push_pop = fun {
    val in = IO(Input(dataType))
    val out = IO(Output(dataType))
    mem.write(read + count, in)
    out := mem.read(read)
    read := read + 1.U
  }

  val idle = fun()
}



class FifoSpec extends FlatSpec {
  Driver.elaborate(() => new UntimedFifo(depth=8, dataType = UInt(8.W)))
}
