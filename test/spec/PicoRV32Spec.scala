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

class MulProtocols[M <: PCPIModule](impl: M) extends ProtocolSpec[Multiplier] {
  val spec = new Multiplier

  def mulProtocol(io: PCPI, clock: Clock, op: String, rs1: UInt, rs2: UInt, rd: UInt): Unit = {
    val instr = ("b" + "0000001" + "0000000000" + op + "00000" + "0110011").U

    io.valid.set(true.B)
    io.insn.set(instr)
    println(s"instruction: ${instr.litValue()}")
    io.rs1.set(rs1)
    io.rs2.set(rs2)
    io.wr.expect(false.B)
    io.ready.expect(false.B)
    clock.step()
    do_while(!io.ready.get(), max=70) {
      clock.step()
    }
    io.rd.expect(rd)
    io.wr.expect(true.B)
    clock.step()
    io.valid.set(false.B)
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

class PicoRV32Spec extends FlatSpec {
  "PicoRV32Mul" should "refine its spec" in {
    Paso(new PicoRV32Mul())(new MulProtocols(_)).proof(new ProofCollateral(_, _){
      invariances { dut =>
        assert(dut.mulWaiting)
        assert(!dut.mulFinishDelay)
        assert(!dut.mulFinish)
        assert(!dut.doWait)
      }
    })
  }
}
