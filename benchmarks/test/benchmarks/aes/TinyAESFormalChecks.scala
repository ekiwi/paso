package benchmarks.aes

import org.scalatest.flatspec.AnyFlatSpec
import paso._
import chisel3._


class TinyAESFormalChecks extends AnyFlatSpec {
  // TODO: seed up proofs!

  "TinyAES OneRound" should "refine its spec" ignore {
    Paso(new OneRound)(new TinyAESRoundProtocol(_)).proof()
  }

  "TinyAES FinalRound" should "refine its spec" ignore {
    Paso(new FinalRound)(new TinyAESRoundProtocol(_)).proof()
  }

  "TinyAES ExpandKey128" should "refine its spec" in {
    StaticTables.rcon.foreach { ii =>
      val rc = ii.U(8.W)
      Paso(new ExpandKey128(rc))(new TinyAESExpandKeyProtocol(_)).proof()
    }
  }

  "TinyAES128" should "correctly connect all submodules" ignore {
    Paso(new TinyAES128)(new TinyAESProtocol(_))(new SubSpecs(_, _) {
      replace(impl.finalRound)(new TinyAESRoundProtocol(_)).bind(spec.finalRound)
      impl.rounds.foreach(r => replace(r)(new TinyAESRoundProtocol(_)).bind(spec.round))
      impl.expandKey.zip(spec.expand).foreach{ case (i,s) => replace(i)(new TinyAESExpandKeyProtocol(_)).bind(s) }
    }).proof(Paso.MCYices2)
  }
}

class TinyAESRandomChecks extends AnyFlatSpec {
  "TinyAES OneRound" should "pass a random test" in {
    Paso(new OneRound)(new TinyAESRoundProtocol(_)).randomTest(1000)
  }

  "TinyAES FinalRound" should "pass a random test" in {
    Paso(new FinalRound)(new TinyAESRoundProtocol(_)).randomTest(1000)
  }

  "TinyAES ExpandKey128" should "pass a random test" in {
    StaticTables.rcon.foreach { ii =>
      val rc = ii.U(8.W)
      Paso(new ExpandKey128(rc))(new TinyAESExpandKeyProtocol(_)).randomTest(100)
    }
  }

  "TinyAES128" should "pass a random test" in {
    Paso(new TinyAES128)(new TinyAESProtocol(_)).randomTest(100)
  }
}
