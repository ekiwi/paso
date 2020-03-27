package spec

import chisel3._
import paso._
import impl._
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
  def mulProtocol(dut: PCPIModule, op: String, rs1: BigInt, rs2: BigInt, rd: BigInt): Unit = {
    val instr = "0000001" + "0000000000" + op + "00000" + "0110011"
    require(instr.length == 32)

    dut.io.valid.poke(true.B)
    dut.io.insn.poke(("b" + instr).U)
    dut.io.rs1.poke(rs1.U)
    dut.io.rs2.poke(rs2.U)
    dut.io.wr.expect(false.B)
    dut.io.ready.expect(false.B)
    dut.clock.step()
    while(!dut.io.ready.peek().litToBoolean) {
      dut.clock.step()
    }
    dut.io.rd.expect(rd.U)
    dut.io.wr.expect(true.B)
    dut.io.valid.poke(false.B)
    dut.clock.step()
  }

  val MUL    = "000" // lower 32bits
  val MULH   = "001" // upper 32bits   signed x signed
  val MULHU  = "011" // upper 32bits unsigned x unsigned
  val MULHSU = "010" // upper 32bits   signed x unsigned

  protocol(spec.mul)(impl.io) { (dut, in, out) =>    mulProtocol(dut, MUL, in.a, in.b, out) }
  protocol(spec.mulh)(impl.io) { (dut, in, out) =>   mulProtocol(dut, MULH, in.a, in.b, out) }
  protocol(spec.mulhu)(impl.io) { (dut, in, out) =>  mulProtocol(dut, MULHU, in.a, in.b, out) }
  protocol(spec.mulhsu)(impl.io) { (dut, in, out) => mulProtocol(dut, MULHSU, in.a, in.b, out) }
}

class MulInductive(impl: PicoRV32Mul, spec: Multiplier) extends MulProtocols(impl, spec) {
  invariances { dut =>
    assert(dut.mulWaiting)
  }
}


class PicoRV32Spec {
  val p = Elaboration[PicoRV32Mul, Multiplier](new PicoRV32Mul(), new Multiplier, (impl, spec) => new MulInductive(impl, spec))
  VerificationProblem.verify(p)
}
