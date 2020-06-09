// Copyright 2020, SiFive, Inc
// released under Apache License Version 2.0
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package untimed

import chisel3._
import org.scalatest._
import paso.UntimedModule


class UntimedInc extends UntimedModule {
  val inc = fun("inc").in(UInt(32.W)).out(UInt(32.W)) {
    (in, out) => out := in + 1.U
  }
}

class UntimedModuleSpec extends FlatSpec {
  "a simple UntimedModule" should "be elaborated with UntimedModule(new ...)" in {
    val m = UntimedModule(new UntimedInc)
    assert(m.isElaborated)
    assert(m.getName == "UntimedInc")
    assert(m.methods.size == 1)
    val inc = m.methods.head
    assert(inc.name == "inc")
  }
}
