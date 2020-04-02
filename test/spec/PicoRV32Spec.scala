package spec

import chisel3._
import paso._
import impl._
import org.scalatest._
import paso.chisel.Elaboration
import paso.verification.VerificationProblem



class Multiplier extends UntimedModule {
  class Args extends Bundle { val a = UInt(32.W) ; val b = UInt(32.W) }
  val mul = fun("mul").in(new Args).out(UInt(32.W)){ (in, out) =>
    out := in.a * in.b
  }
  val mulh = fun("mulh").in(new Args).out(UInt(32.W)){ (in, out) =>
    out := (in.a.asSInt() * in.b.asSInt()).asUInt()(63,32)
  }
  val mulhu = fun("mulhu").in(new Args).out(UInt(32.W)){ (in, out) =>
    out := (in.a * in.b)(63,32)
  }
  val mulhsu = fun("mulhsu").in(new Args).out(UInt(32.W)){ (in, out) =>
    out := (in.a.asSInt() * ("b0".U ## in.b).asSInt()).asUInt()(63,32)
  }
}

class MulProtocols[M <: PCPIModule](impl: M, spec: Multiplier) extends Binding(impl, spec) {
  def mulProtocol(io: PCPI, clock: Clock, op: String, rs1: UInt, rs2: UInt, rd: UInt): Unit = {
    val instr = ("b" + "0000001" + "0000000000" + op + "00000" + "0110011").U

    io.valid.poke(true.B)
    io.insn.poke(instr)
    io.rs1.poke(rs1)
    io.rs2.poke(rs2)
    io.wr.expect(false.B)
    io.ready.expect(false.B)
    clock.step()
    do_while(!io.ready.peek(), max=20) {
      clock.step()
    }
    io.valid.poke(false.B)
    io.rd.expect(rd)
    io.wr.expect(true.B)
    clock.step()
  }

  val MUL    = "000" // lower 32bits
  val MULH   = "001" // upper 32bits   signed x signed
  val MULHU  = "011" // upper 32bits unsigned x unsigned
  val MULHSU = "010" // upper 32bits   signed x unsigned

  protocol(spec.mul)(impl.io) { (clock, dut, in, out) =>    mulProtocol(dut, clock, MUL, in.a, in.b, out) }
  protocol(spec.mulh)(impl.io) { (clock, dut, in, out) =>   mulProtocol(dut, clock, MULH, in.a, in.b, out) }
  protocol(spec.mulhu)(impl.io) { (clock, dut, in, out) =>  mulProtocol(dut, clock, MULHU, in.a, in.b, out) }
  protocol(spec.mulhsu)(impl.io) { (clock, dut, in, out) => mulProtocol(dut, clock, MULHSU, in.a, in.b, out) }
}

class MulInductive(impl: PicoRV32Mul, spec: Multiplier) extends MulProtocols(impl, spec) {
  invariances { dut =>
    assert(dut.mulWaiting)
    assert(!dut.mulFinishDelay)
  }
}


class PicoRV32Spec extends FlatSpec {
  val p = Elaboration[PicoRV32Mul, Multiplier](new PicoRV32Mul(), new Multiplier, (impl, spec) => new MulInductive(impl, spec))
  VerificationProblem.verify(p)
}
