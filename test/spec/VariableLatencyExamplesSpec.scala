package spec

import chisel3._
import chisel3.util._
import paso._
import org.scalatest._
import paso.chisel.Elaboration
import paso.verification.VerificationProblem

/** Simply returns the input unmodified */
class Identity[D <: Data](dataType: D) extends UntimedModule {
  val id = fun("id").in(dataType).out(dataType) { (in, out) => out := in }
  val idle = fun("idle") {}
}

class IdentityAndKeep[D <: Data](dataType: D) extends UntimedModule {
  val valid = RegInit(false.B)
  val value = Reg(dataType)
  val id = fun("id").in(dataType).out(dataType) { (in, out) =>
    out := in
    valid := true.B
    value := in
  }
  val idle = fun("idle").out(UInt(32.W)) { out =>
    when(valid) {
      out := value
    }.otherwise {
      out := DontCare
    }
  }
}

class VariableLatencyIO extends Bundle {
  val start = Input(Bool())
  val done = Output(Bool())
  val dataIn = Input(UInt(32.W))
  val dataOut = Output(UInt(32.W))
}

abstract class VariableLatencyModule extends Module {
  val io = IO(new VariableLatencyIO)
}

class RandomLatency(maxLatency: Int = 4) extends VariableLatencyModule {
  val buffer = Reg(UInt(32.W))
  when(io.start) {
    buffer := io.dataIn
  }

  val counterTyp = UInt(log2Ceil(maxLatency).W)
  val delay = RegInit(counterTyp, 1.U) // unfortunately yosys compiles an uninitialized Reg into an input when emitting btor2, why?
  val counter = Reg(counterTyp)
  counter := Mux(io.start, 0.U, counter + 1.U)

  val running = RegInit(false.B)
  val done = running && (counter === delay)
  when(io.start) {
    running := true.B
  }
    .elsewhen(done) {
      running := false.B
    }

  io.done := done
  io.dataOut := Mux(done, buffer, 0.U)
}

class DataDependentLatency(maxLatency: Int = 4) extends RandomLatency(maxLatency) {
  // use lower bits of dataIn to set the delay
  when(io.start) {
    delay := io.dataIn
  }
}

class RandomLatencyKeepOutput(maxLatency: Int = 4) extends RandomLatency(maxLatency) {
  // this keeps the output available until the next `id` transaction
  io.dataOut := buffer
}

class RandomLatencyProtocols(impl: VariableLatencyModule) extends ProtocolSpec[Identity[UInt]] {
  // derive specification parameter from implementation
  // this allows us to verify generators in multiple different configurations
  val spec = new Identity(chiselTypeOf(impl.io.dataIn))

  protocol(spec.id)(impl.io) { (clock, dut, in, out) =>
    dut.start.set(true.B)
    dut.dataIn.set(in)
    dut.done.expect(false.B)
    clock.step()

    dut.start.set(false.B)
    dut.dataIn.set(DontCare)
    do_while(!dut.done.get(), max = 4) {
      clock.step()
    }

    dut.dataOut.expect(out)
    clock.step()
  }
  protocol(spec.idle)(impl.io) { (clock, dut) =>
    dut.start.set(false.B)
    clock.step()
  }
}

class VariableLatencyKeepProtocols(impl: VariableLatencyModule) extends ProtocolSpec[IdentityAndKeep[UInt]] {
  val spec = new IdentityAndKeep(chiselTypeOf(impl.io.dataIn))

  protocol(spec.id)(impl.io) { (clock, dut, in, out) =>
    dut.start.set(true.B)
    dut.dataIn.set(in)
    dut.done.expect(false.B)
    clock.step()

    dut.start.set(false.B)
    dut.dataIn.set(DontCare)
    do_while(!dut.done.get(), max = 4) {
      clock.step()
    }

    dut.dataOut.expect(out)
    clock.step()
  }
  protocol(spec.idle)(impl.io) { (clock, dut, out) =>
    dut.start.set(false.B)
    dut.dataOut.expect(out)
    clock.step()
  }
}

class ConstLatencyIO extends Bundle {
  val start = Input(Bool())
  val dataIn = Input(UInt(64.W))
  val dataOut = Output(UInt(64.W))
}

// this module employs two buffers to save the results from the two variable latency units
class VariableLatencyToConst extends Module {
  val io = IO(new ConstLatencyIO)

  val lsb = Module(new RandomLatency)
  lsb.io.start := io.start
  lsb.io.dataIn := io.dataIn(31, 0)
  val lsbBuffer = RegEnable(lsb.io.dataOut, lsb.io.done)

  val msb = Module(new RandomLatency)
  msb.io.start := io.start
  msb.io.dataIn := io.dataIn(63, 32)
  val msbBuffer = RegEnable(msb.io.dataOut, msb.io.done)

  // bypass
  val latestLsb = Mux(lsb.io.done, lsb.io.dataOut, lsbBuffer)
  val latestMsb = Mux(msb.io.done, msb.io.dataOut, msbBuffer)

  io.dataOut := latestMsb ## latestLsb
}

// this module does not need any memory since it relies on its sub modules to keep their last output constant
class VariableLatencyKeepToConst extends Module {
  val io = IO(new ConstLatencyIO)

  val lsb = Module(new RandomLatencyKeepOutput)
  lsb.io.start := io.start
  lsb.io.dataIn := io.dataIn(31, 0)

  val msb = Module(new RandomLatencyKeepOutput)
  msb.io.start := io.start
  msb.io.dataIn := io.dataIn(63, 32)

  io.dataOut := msb.io.dataOut ## lsb.io.dataOut
}

//class VariableLatencyToConstSubspecs(impl: VariableLatencyToConst) extends SubspecBindings {
//  replace(impl.lsb)(new RandomLatencyProtocols(_))
//  replace(impl.msb)(new RandomLatencyProtocols(_))
//}


class VariableLatencyExamplesSpec extends FlatSpec {
  "RandomLatency module" should "refine its spec" in {
    Paso.proof(new RandomLatency)(new RandomLatencyProtocols(_))(new ProofCollateral(_, _){
      invariances { dut => assert(!dut.running)  }
    }).run()
  }

  "RandomLatencyAndKeep module" should "refine its spec" in {
    Paso.proof(new RandomLatencyKeepOutput)(new VariableLatencyKeepProtocols(_))(new ProofCollateral(_, _){
      invariances { dut => assert(!dut.running) }
      mapping { (impl, spec) =>
        when(spec.valid) {
          assert(impl.buffer === spec.value)
        }
      }
    }).run()
  }
}
