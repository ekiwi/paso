import chisel3._
import chisel3.util._

import org.scalatest._

class UntimedModule extends RawModule {
//  def fun(inputs: => Unit) = ???
//  def fun(inputs: => Unit)(outputs: => Unit) = ???
//
//  def method(name: String)(foo: => Unit) = ???

  def fun() = ???
  def fun[I <: Bundle](foo: I => Unit) = ???
  def fun[I <: Bundle, O <: Bundle](foo: (I, O) => Unit) = ???

}



class UntimedFifo[G <: Data](val depth: Int, dataType: G) extends UntimedModule {
  require(depth > 0)
  val mem = Mem(depth, dataType)
  val count = Reg(UInt((log2Ceil(depth) + 1).W))
  val read = Reg(UInt(log2Ceil(depth).W))
  val full = count === depth.U
  val empty = count === 0.U

  class Input extends Bundle { val in = dataType }
  class Output extends Bundle { val out = dataType }

  val push = fun { in: Input =>
    mem.write(read + count, in.in)
    count := count + 1.U
  }

  val pop = fun { (_: Bundle, out: Output) =>
    out := mem.read(read)
    count := count - 1.U
    read := read + 1.U
  }

  val push_pop = fun { (in: Input, out: Output) =>
    mem.write(read + count, in.in)
    out := mem.read(read)
    read := read + 1.U
  }

  val idle = fun()
}



class FifoSpec extends FlatSpec {

}
