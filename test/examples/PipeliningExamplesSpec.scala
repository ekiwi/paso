package examples

import chisel3._
import chisel3.util._
import org.scalatest._
import paso._

class IdentityNoIdle[D <: Data](dataType: D) extends UntimedModule {
  val id = fun("id").in(dataType).out(dataType) { (in, out) => out := in }
}

class Register extends Module {
  val io = IO(new Bundle{
    val in = Input(UInt(32.W))
    val out = Output(UInt(32.W))
  })
  io.out := RegNext(io.in)
}

class RegisterProtocol(impl: Register) extends ProtocolSpec[IdentityNoIdle[UInt]] {
  val spec = new IdentityNoIdle[UInt](chiselTypeOf(impl.io.in))

  protocol(spec.id)(impl.io) { (clock, dut, in, out) =>
    dut.in.set(in)
    clock.step() // this is a short-hand for clock.stepAndFork() because we assert an output with no following step
    dut.out.expect(out)
  }
}

class PipeliningExamplesSpec extends FlatSpec {
  "A simple register" should "refine its spec" in {
    Paso(new Register)(new RegisterProtocol(_)).proof()
  }
}
