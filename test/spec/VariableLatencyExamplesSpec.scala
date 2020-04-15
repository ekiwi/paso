package spec

import chisel3._
import chisel3.util._
import paso._
import org.scalatest._
import paso.chisel.Elaboration
import paso.verification.VerificationProblem

/** Simply returns the input unmodified */
class Identity extends UntimedModule {
  val id = fun("id").in(UInt(32.W)).out(UInt(32.W)){ (in, out) => out := in }
  val idle = fun("idle"){}
}

class IdentityAndKeep extends UntimedModule {
  val valid = RegInit(false.B)
  val value = Reg(UInt(32.W))
  val id = fun("id").in(UInt(32.W)).out(UInt(32.W)){ (in, out) =>
    out := in
    valid := true.B
    value := in
  }
  val idle = fun("idle").out(UInt(32.W)){ out =>
    when(valid) { out := value } .otherwise { out := DontCare }
  }
}

class VariableLatencyIO extends Bundle {
  val start = Input(Bool())
  val done = Output(Bool())
  val dataIn = Input(UInt(32.W))
  val dataOut = Output(UInt(32.W))
}

abstract class VariableLatencyModule extends Module { val io = IO(new VariableLatencyIO) }

class RandomLatency(maxLatency: Int = 4) extends VariableLatencyModule {
  val buffer = Reg(UInt(32.W))
  when(io.start) { buffer := io.dataIn }

  val counterTyp = UInt(log2Ceil(maxLatency).W)
  val delay = RegInit(counterTyp, 1.U) // unfortunately yosys compiles an uninitialized Reg into an input when emitting btor2, why?
  val counter = Reg(counterTyp)
  counter := Mux(io.start, 0.U, counter + 1.U)

  val running = RegInit(false.B)
  val done = running && (counter === delay)
  when(io.start) { running := true.B }
    .elsewhen(done) { running := false.B }

  io.done := done
  io.dataOut := Mux(done, buffer, 0.U)
}

class DataDependentLatency(maxLatency: Int = 4) extends RandomLatency(maxLatency) {
  // use lower bits of dataIn to set the delay
  when(io.start) { delay := io.dataIn }
}

class RandomLatencyKeepOutput(maxLatency: Int = 4) extends RandomLatency(maxLatency) {
  // this keeps the output available until the next `id` transaction
  io.dataOut := buffer
}

class RandomLatencyProtocols[F <: VariableLatencyModule](impl: F, spec: Identity) extends Binding(impl, spec) {
  protocol(spec.id)(impl.io) { (clock, dut, in, out) =>
    dut.start.poke(true.B)
    dut.dataIn.poke(in)
    dut.done.expect(false.B)
    clock.step()

    dut.start.poke(false.B)
    dut.dataIn.poke(DontCare)
    do_while(!dut.done.peek(), max=4) {
      clock.step()
    }

    dut.dataOut.expect(out)
    clock.step()
  }
  protocol(spec.idle)(impl.io) { (clock, dut) =>
    dut.start.poke(false.B)
    clock.step()
  }
}

class RandomLatencyInductive(impl: RandomLatency, spec: Identity) extends RandomLatencyProtocols(impl, spec) {
  invariances { dut => assert(!dut.running)  }
}

class VariableLatencyKeepProtocols[F <: VariableLatencyModule](impl: F, spec: IdentityAndKeep) extends Binding(impl, spec) {
  protocol(spec.id)(impl.io) { (clock, dut, in, out) =>
    dut.start.poke(true.B)
    dut.dataIn.poke(in)
    dut.done.expect(false.B)
    clock.step()

    dut.start.poke(false.B)
    dut.dataIn.poke(DontCare)
    do_while(!dut.done.peek(), max=4) {
      clock.step()
    }

    dut.dataOut.expect(out)
    clock.step()
  }
  protocol(spec.idle)(impl.io) { (clock, dut, out) =>
    dut.start.poke(false.B)
    dut.dataOut.expect(out)
    clock.step()
  }
}

class VariableLatencyKeepInductive(impl: RandomLatencyKeepOutput, spec: IdentityAndKeep) extends VariableLatencyKeepProtocols(impl, spec) {
  invariances { dut => assert(!dut.running)  }
  mapping { (impl, spec) => when(spec.valid) { assert(impl.buffer === spec.value) } }
}


class VariableLatencyExamplesSpec extends FlatSpec {
  "RandomLatency module" should "refine its spec" in {
    val p = Elaboration()[RandomLatency, Identity](new RandomLatency, new Identity, (impl, spec) => new RandomLatencyInductive(impl, spec))
    VerificationProblem.verify(p)
  }

  "RandomLatencyAndKeep module" should "refine its spec" in {
    val p = Elaboration()[RandomLatencyKeepOutput, IdentityAndKeep](new RandomLatencyKeepOutput, new IdentityAndKeep, (impl, spec) => new VariableLatencyKeepInductive(impl, spec))
    VerificationProblem.verify(p)
  }
}
