package spec

import chisel3._
import paso._
import impl._
import org.scalatest._
import paso.chisel.Elaboration
import paso.verification.VerificationProblem


// this is based on a translation of the ILA from
// https://github.com/PrincetonUniversity/IMDb/tree/master/tutorials/aes
class AESKeyExpansionSpec(rc: UInt) extends UntimedModule with AESHelperFunctions {
  require(rc.getWidth == 8)

  val expandKey128 = fun("expandKey128").in(UInt(128.W)).out(UInt(128.W)) { (in, out) =>
    val K = slice128To32(in)
    val v0 = K(0)(31, 24) ^ rc ## K(0)(23,0)
    val v1 = v0 ^ K(1)
    val v2 = v1 ^ K(2)
    val v3 = v2 ^ K(3)

    val k0a = v0
    val k1a = v1
    val k2a = v2
    val k3a = v3

    val k4a = S4(K(3)(23, 0) ## K(3)(31, 24))

    val k0b = k0a ^ k4a
    val k1b = k1a ^ k4a
    val k2b = k2a ^ k4a
    val k3b = k3a ^ k4a

    out := k0b ## k1b ## k2b ## k3b
  }
}

class RoundIn extends Bundle {
  val key = UInt(128.W)
  val state = UInt(128.W)
}
trait IsRoundSpec extends UntimedModule{ val round : IOMethod[RoundIn, UInt]  }

class AESRoundSpec extends UntimedModule with AESHelperFunctions with IsRoundSpec {
  val round= fun("round").in(new RoundIn).out(UInt(128.W)) { (in, nextState) =>
    val K0_4 = slice128To32(in.key)
    val S0_4 = slice128To32(in.state)

    val p0 = tableLookup(S0_4(0))
    val p1 = tableLookup(S0_4(1))
    val p2 = tableLookup(S0_4(2))
    val p3 = tableLookup(S0_4(3))

    val z0 = p0(0) ^ p1(1) ^ p2(2) ^ p3(3) ^ K0_4(0)
    val z1 = p0(3) ^ p1(0) ^ p2(1) ^ p3(2) ^ K0_4(1)
    val z2 = p0(2) ^ p1(3) ^ p2(0) ^ p3(1) ^ K0_4(2)
    val z3 = p0(1) ^ p1(2) ^ p2(3) ^ p3(0) ^ K0_4(3)

    nextState := z0 ## z1 ## z2 ## z3
  }
}

class AESFinalRoundSpec extends UntimedModule with AESHelperFunctions with IsRoundSpec {
  val round = fun("round").in(new RoundIn).out(UInt(128.W)) { (in, nextState) =>
    val K0_4 = slice128To32(in.key)
    val S0_4 = slice128To32(in.state)

    val p0 = slice32To8(S4(S0_4(0)))
    val p1 = slice32To8(S4(S0_4(1)))
    val p2 = slice32To8(S4(S0_4(2)))
    val p3 = slice32To8(S4(S0_4(3)))

    val z0 = (p0(0) ## p1(1) ## p2(2) ## p3(3)) ^ K0_4(0)
    val z1 = (p1(0) ## p2(1) ## p3(2) ## p0(3)) ^ K0_4(1)
    val z2 = (p3(0) ## p3(1) ## p0(2) ## p1(3)) ^ K0_4(2)
    val z3 = (p0(0) ## p0(1) ## p1(2) ## p2(3)) ^ K0_4(3)

    nextState := z0 ## z1 ## z2 ## z3
  }
}

class TinyAESRoundProtocol(impl: HasRoundIO, spec: IsRoundSpec) extends Binding(impl, spec) {
  protocol(spec.round)(impl.io) { (clock, dut, in, out) =>
    dut.key.poke(in.key)
    dut.state.poke(in.state)
    clock.step()
    dut.key.poke(DontCare)
    dut.state.poke(DontCare)
    dut.stateNext.expect(out)
  }
}

class TinyAESExpandKeyProtocol(impl: ExpandKey128, spec: AESKeyExpansionSpec) extends Binding(impl, spec) {
  protocol(spec.expandKey128)(impl.io) { (clock, dut, in, out) =>
    dut.in.poke(in)
    clock.step()
    dut.in.poke(DontCare)
    dut.out.expect(out)
    clock.step()
    dut.outDelayed.expect(out)
  }

}



class TinyAESSpec extends FlatSpec {
  "TinyAES OneRound" should "refine its spec" in {
    val p = Elaboration()[HasRoundIO, IsRoundSpec](new OneRound, new AESRoundSpec, (impl, spec) => new TinyAESRoundProtocol(impl, spec))
    VerificationProblem.verify(p)
  }

  "TinyAES FinalRound" should "refine its spec" in {
    val p = Elaboration()[HasRoundIO, IsRoundSpec](new FinalRound, new AESFinalRoundSpec, (impl, spec) => new TinyAESRoundProtocol(impl, spec))
    VerificationProblem.verify(p)
  }

}
