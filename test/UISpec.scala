// See LICENSE for license details.

import org.scalatest.{FlatSpec, FreeSpec, Matchers}
import chisel3._

/**
 * = Notebook =
 *
 * == 2019-Aug-30 ==
 * - ideally the add functional semantics could be specified something like this:
 *   `def add(a: UInt(width.W), b: UInt(width.w)) -> (c: UInt(width.w)) = { c:= a + b}`
 * - but maybe it is better to start with the Protocol
 * - thus the dependencies would be [[Bundle]] <- [[Protocol]] <- [[Transaction]]
 * - Protocols will only ever work with a particular bundle since they need to refer to the exact pins
 * - multiple Transactions might use the same Protocol, thus it would make sense to declare the functional I/O
 *   in the Protocol instead of the Transaction
 *
 * == 2019-Sep-03 ==
 * - abandoning this for now
 * - there are too many open questions about composability, e.g., should a spec be able to refer to other
 *   specs from its submodules? Something like `res = alu.add(a,b)`?
 *
 *
 *
 */


abstract class Transaction extends Module {
}


trait IsProtocol

abstract class Protocol[T <: Bundle](io: T) extends RawModule with IsProtocol {
  def step(): Unit = { println("TODO: implement Protocol.step") }
  def apply(spec: this.type => Unit): Unit = {
    spec(this)
  }
}

abstract class Spec {

}

class Function[P <: IsProtocol](val exec: P => Unit) {
  //def apply()
}

object fun {
  def apply[P <: IsProtocol](exec: P => Unit): Function[P] = {
    new Function[P](exec)
  }
}


abstract class ModuleWithSpec extends Module {
  val spec: Spec
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class SerAddProtocol(io: ser_add_io, width: Int) extends Protocol(io) {
  val a = Input(UInt(width.W))
  val b = Input(UInt(width.W))
  val sum = Output(UInt(width.W))
  val carry = Output(UInt(1.W))

  // run protocol
  io.clr := true.B
  step()
  for(ii <- 0 until width) {
    io.clr  := false.B
    io.a    := a(width)
    io.b    := b(width)
    sum(ii) := io.q
    if(ii + 1 == width) carry := io.o_v
    step()
  }
}

class AddSpec(adder: ser_add_io, width: Int) extends Spec {
  val proto = Module(new SerAddProtocol(adder, width))
  val add = proto { p => p.sum := p.a + p.b; p.carry := (p.a +& p.b).head(1) }
}



class ser_add_io extends Bundle {
  val a = Input(UInt(1.W))
  val b = Input(UInt(1.W))
  val clr = Input(Bool())
  val q = Output(UInt(1.W))
  val o_v = Output(UInt(1.W))
}

class ser_add extends Module {
  val io = IO(new ser_add_io)
  //val spec = new AddSpec(io, 8)
  val c_r = RegInit(0.U(1.W))
  val axorb = io.a ^ io.b
  io.o_v := (axorb & c_r) | (io.a & io.b)
  io.q := axorb ^ c_r
  c_r := !io.clr & io.o_v
}

//scalastyle:off magic.number
class UISpec extends FreeSpec with Matchers {

  "elaborate adder" in {
    Driver.elaborate(() => new ser_add)
  }

  "elaborate spec" ignore {
    Driver.elaborate{() =>
      val add = new ser_add
      val spec = new AddSpec(add.io, 8)
      add
    }
  }




}

