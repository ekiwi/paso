package spec

import chisel3._
import paso._
import impl._
import org.scalatest._
import paso.chisel.Elaboration
import paso.verification.VerificationProblem


trait AESHelperFunctions {
  def slice128To32(u: UInt): Seq[UInt] = {
    require(u.getWidth == 128)
    Seq(u(127,96), u(95, 64), u(63,32), u(31, 0))
  }

  def slice32To8(u: UInt): Seq[UInt] = {
    require(u.getWidth == 32)
    Seq(u(31,24), u(23, 16), u(15,8), u(7, 0))
  }

  def selectFromArray(i: UInt, data: Seq[UInt]): UInt = {
    data.zipWithIndex.foldLeft[UInt](data.head){case (prev, (value, index)) => Mux(i === index.U, value, prev)}
  }

  def S(i: UInt): UInt = {
    require(i.getWidth == 8)
    selectFromArray(i, StaticTables.S.map(_.U(8.W)))
  }

  def xS(i: UInt): UInt = {
    require(i.getWidth == 8)
    selectFromArray(i, StaticTables.xS.map(_.U(8.W)))
  }

  def S4(u: UInt): UInt = {
    require(u.getWidth == 32)
    S(u(31, 24)) ## S(u(23, 16)) ## S(u(15, 8)) ## S(u(7,0))
  }

  def T(u : UInt): Seq[UInt] = {
    require(u.getWidth == 8)
    val sl0 = S(u)
    val sl1 = sl0
    val sl3 = xS(u)
    val sl2 = sl1 ^ sl3

    Seq(sl0, sl1, sl2, sl3)
  }

  def expandKey128B(in: UInt, rc: UInt): UInt = {
    require(in.getWidth == 128)
    require(rc.getWidth == 8)

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

    k0b ## k1b ## k2b ## k3b
  }

  def tableLookup(s32: UInt): UInt = {
    val b = slice32To8(s32)
    var rl = T(b(0))
    val p0 = rl(3) ## rl(0) ## rl(1) ## rl(2)
    rl = T(b(1))
    val p1 = rl(2) ## rl(3) ## rl(0) ## rl(1)
    rl = T(b(1))
    val p2 = rl(1) ## rl(2) ## rl(3) ## rl(0)
    rl = T(b(1))
    val p3 = rl(0) ## rl(1) ## rl(2) ## rl(3)

    p0 ## p1 ## p2 ## p3
  }
}

// this is a translation of the ILA from
// https://github.com/PrincetonUniversity/IMDb/tree/master/tutorials/aes
class AESSpec extends UntimedModule with AESHelperFunctions {
  val cipherText = Reg(UInt(128.W))
  val roundKey = Reg(UInt(128.W))
  val round = RegInit(0.U(4.W))

  class In extends Bundle {
    val key = UInt(128.W)
    val plainText = UInt(128.W)
  }

  val firstRound = fun("firstRound").in(new In).when(round === 0.U){ in =>
    cipherText := in.key ^ in.plainText
    roundKey := in.key
    round := 1.U
  }

  val midRound = fun("midRound").when(round > 0.U && round < 10.U) {
    val rcon = selectFromArray(round - 1.U, StaticTables.rcon.map(_.U(8.W)))
    val encKey = expandKey128B(roundKey, rcon)
    val K0_4 = slice128To32(encKey)
    val S0_4 = slice128To32(cipherText)

    val p0 = tableLookup(S0_4(0))
    val p1 = tableLookup(S0_4(1))
    val p2 = tableLookup(S0_4(2))
    val p3 = tableLookup(S0_4(3))

    val z0 = p0(0) ^ p1(1) ^ p2(2) ^ p3(3) ^ K0_4(0)
    val z1 = p0(3) ^ p1(0) ^ p2(1) ^ p3(2) ^ K0_4(1)
    val z2 = p0(2) ^ p1(3) ^ p2(0) ^ p3(1) ^ K0_4(2)
    val z3 = p0(1) ^ p1(2) ^ p2(3) ^ p3(0) ^ K0_4(3)

    cipherText := z0 ## z1 ## z2 ## z3
    roundKey := expandKey128B(roundKey, rcon)

    round := round + 1.U
  }

  val finalRound = fun("finalRound").out(UInt(128.W)).when(round === 10.U) { out =>
    val encKey = expandKey128B(roundKey, StaticTables.rcon(9).U(8.W))
    val K0_4 = slice128To32(encKey)
    val S0_4 = slice128To32(cipherText)

    val p0 = slice32To8(S4(S0_4(0)))
    val p1 = slice32To8(S4(S0_4(1)))
    val p2 = slice32To8(S4(S0_4(2)))
    val p3 = slice32To8(S4(S0_4(3)))

    val z0 = (p0(0) ## p1(1) ## p2(2) ## p3(3)) ^ K0_4(0)
    val z1 = (p1(0) ## p2(1) ## p3(2) ## p0(3)) ^ K0_4(1)
    val z2 = (p3(0) ## p3(1) ## p0(2) ## p1(3)) ^ K0_4(2)
    val z3 = (p0(0) ## p0(1) ## p1(2) ## p2(3)) ^ K0_4(3)

    out := z0 ## z1 ## z2 ## z3
    round := 0.U // there seems to be a bug in the ILA where round is further incremented!
  }
}

class TinyAESProtocols(impl: TinyAES128) extends ProtocolSpec[AESSpec] {
  val spec = new AESSpec

  protocol(spec.firstRound)(impl.io) { (clock, dut, in) =>
    dut.key := in.key
    dut.state := in.plainText
    clock.step()
    dut.key.poke(DontCare)
    dut.state.poke(DontCare)
    clock.step()
  }
  protocol(spec.midRound)(impl.io) { (clock, _) => clock.step() ; clock.step() }
  protocol(spec.finalRound)(impl.io) { (clock, dut, out) =>
    clock.step()
    clock.step()
    dut.out.expect(out)
  }
}

class TinyAESRoundBasedSpec extends FlatSpec {
  "TinyAES" should "refine its spec" in {
    Paso(new TinyAES128)(new TinyAESProtocols(_)).proof(new ProofCollateral(_, _) {
      mapping { (impl, spec) =>
        (1 until 11).foreach { ii =>
          when(spec.round === ii.U) {
            assert(spec.cipherText === impl.s(ii - 1))
            assert(spec.roundKey === impl.k(ii - 1))
          }
        }
      }
    })
  }
}
