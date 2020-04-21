package spec

import chisel3._
import paso._
import impl._
import org.scalatest._
import paso.chisel.Elaboration
import paso.verification.VerificationProblem

// this is a translation of the ILA from
// https://github.com/PrincetonUniversity/IMDb/tree/master/tutorials/aes
class AESSpec extends UntimedModule {
  val cipherText = Reg(UInt(128.W))
//  val cipherTextValid = RegInit(false.B)
  val roundKey = Reg(UInt(128.W))
//  val roundKeyValid = RegInit(false.B)
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
    cipherText := ???
    roundKey := ???
    round := round + 1.U
  }

  val finalRound = fun("finalRound").out(128.W).when(round === 10.U) { out =>
    out := ???
    round := 0.U // there seems to be a bug in the ILA where round is further incremented!
  }
}


class TinyAESSpec {

}
