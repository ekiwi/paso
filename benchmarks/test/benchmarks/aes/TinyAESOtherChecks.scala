package benchmarks.aes

import chisel3._
import org.scalatest.flatspec.AnyFlatSpec
import paso._

// contains formal verification collateral that isn't part of the central AES correctness proof

class AESTableLookup extends UntimedModule with AESHelperFunctions {
  val lookup = fun("lookup").in(UInt(32.W)).out(Vec(4, UInt(32.W))) { (in, out) =>
    out := tableLookup(in)
  }
}
class TinyAESTableLookupProtocol(impl: TableLookup) extends ProtocolSpec[AESTableLookup] {
  val spec = new AESTableLookup
  override val stickyInputs = false
  protocol(spec.lookup)(impl.io) { (clock, dut, in, out) =>
    dut.state.poke(in)
    clock.stepAndFork()
    dut.p(0).expect(out(0))
    dut.p(1).expect(out(1))
    dut.p(2).expect(out(2))
    dut.p(3).expect(out(3))
    clock.step()
  }
}

class AES128DebugSpec extends UntimedModule with AESHelperFunctions {
  val round = UntimedModule(new AESRoundSpec)
  val expand = UntimedModule(new AESKeyExpansionSpec(rcon(0).U(8.W)))

  val aes128 = fun("aes128").in(new RoundIn).out(UInt(128.W)) { (in, out) =>
    val r = Wire(new RoundIn)
    // expand key
    r.key := expand.expandKey128(in.key)
    r.state := in.state ^ in.key
    out := round.round(r)
  }
}

class TinyAES128Debug extends Module {
  val io = IO(new TinyAES128IO)
  val s0 = RegNext(io.state ^ io.key)
  val k0 = RegNext(io.key)

  val k1 = Wire(UInt(128.W))
  val k0b = Wire(UInt(128.W))
  val s1 = Wire(UInt(128.W))

  val a1 = ExpandKey128(StaticTables.rcon(0), k0, k0b, k1)
  val r1 = OneRound(s0, k0b, s1)

  io.out := s1
}

class TinyAESDebugProtocol(impl: TinyAES128Debug) extends ProtocolSpec[AES128DebugSpec] {
  val spec = new AES128DebugSpec
  override val stickyInputs = false

  protocol(spec.aes128)(impl.io) { (clock, dut, in, out) =>
    // apply state and key for one cycle
    dut.state.poke(in.state)
    dut.key.poke(in.key)
    clock.stepAndFork()
    dut.state.poke(DontCare)
    dut.key.poke(DontCare)

    clock.step()
    clock.step()

    dut.out.expect(out)
    clock.step()
  }
}

class TinyAESOtherSpec extends AnyFlatSpec with PasoTester {
  // this was used to hunt down a bug in our spec by breaking it into smaller pieces
  "TinyAES TableLookup" should "refine its spec" in {
    test(new TableLookup)(new TinyAESTableLookupProtocol(_)).proof()
  }

  "TinyAES128Debug" should "correctly connect all submodules" in {
    test(new TinyAES128Debug)(new TinyAESDebugProtocol(_))(new SubSpecs(_, _) {
      replace(impl.r1)(new TinyAESRoundProtocol(_)).bind(spec.round)
      replace(impl.a1)(new TinyAESExpandKeyProtocol(_)).bind(spec.expand)
    }).proof(Paso.MCYices2)
  }
}
