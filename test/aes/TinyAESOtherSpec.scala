package aes

import chisel3._
import org.scalatest._
import paso._

// contains formal verification collateral that isn't part of the central AES correctness proof

class AESTableLookup extends UntimedModule with AESHelperFunctions {
  val lookup = fun("lookup").in(UInt(32.W)).out(Vec(4, UInt(32.W))) { (in, out) =>
    out := tableLookup(in)
  }
}
class TinyAESTableLookupProtocol(impl: TableLookup) extends ProtocolSpec[AESTableLookup] {
  val spec = new AESTableLookup
  protocol(spec.lookup)(impl.io) { (clock, dut, in, out) =>
    dut.state.poke(in)
    clock.step()
    dut.p(0).expect(out(0))
    dut.p(1).expect(out(1))
    dut.p(2).expect(out(2))
    dut.p(3).expect(out(3))
  }
}

class TinyAESOtherSpec extends FlatSpec {
  // this was used to hunt down a bug in our spec by breaking it into smaller pieces
  "TinyAES TableLookup" should "refine its spec" in {
    Paso(new TableLookup)(new TinyAESTableLookupProtocol(_)).proof()
  }

}
