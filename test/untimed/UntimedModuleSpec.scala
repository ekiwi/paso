// Copyright 2020, SiFive, Inc
// released under Apache License Version 2.0
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package untimed

import chisel3._
import org.scalatest.flatspec.AnyFlatSpec
import paso.UntimedModule
import paso.untimed.UntimedError


class UntimedInc extends UntimedModule {
  // a dummy state which will trip our call determinism check (you are not allowed to call more than one method
  // of a stateful module at a single time)
  val dummyState = RegInit(0.U(4.W))
  val inc = fun("inc").in(UInt(32.W)).out(UInt(32.W)) {
    (in, out) => out := in + 1.U
  }
}

class Counter4Bit extends UntimedModule {
  val value = RegInit(0.U(4.W))
  val inc = fun("inc").out(UInt(4.W)) { out =>
    value := value + 1.U
    out := value + 1.U
  }
}

class Counter4BitWithSubModule extends UntimedModule {
  val value = RegInit(0.U(4.W))
  val ii = UntimedModule(new UntimedInc)
  val inc = fun("inc").out(UInt(4.W)) { out =>
    val newValue = ii.inc(value)
    value := newValue
    out := newValue
  }
}



class UntimedIncNoState extends UntimedModule {
  val inc = fun("inc").in(UInt(32.W)).out(UInt(32.W)) {
    (in, out) => out := in + 1.U
  }
}

class Counter4BitWithSubModuleAndTwoCallsNoSubstate extends UntimedModule {
  val value = RegInit(0.U(4.W))
  val ii = UntimedModule(new UntimedIncNoState)
  val inc = fun("inc").out(UInt(4.W)) { out =>
    // because we use a submodule with no substate, calling it twice is fine!
    value := ii.inc(value)
    out := ii.inc(value)
  }
}



class UntimedModuleSpec extends AnyFlatSpec {
  "a simple UntimedModule" should "be elaborated with UntimedModule(new ...)" in {
    val m = UntimedModule(new UntimedInc)
    assert(m.isElaborated)
    assert(m.name == "UntimedInc")
    assert(m.methods.size == 1)
    val inc = m.methods.head
    assert(inc.name == "inc")

    // we should be able to access the low firrtl
    val f = m.getFirrtl
    assert(f.circuit.main == "UntimedInc")
    // as a crude check to see if the circuit is actually in LowForm, make sure there are no whens
    val src = f.circuit.serialize
    assert(!src.contains("when "))
    // there should not be any valid ifs, everything should be deterministic
    assert(!src.contains("validif(inc_enabled"))

    // we should be able to get an interactive treadle tester
    val t = m.getTester
    t.poke("inc_enabled", 1)
    t.poke("inc_arg", 32)
    assert(t.peek("inc_guard") == 1)
    assert(t.peek("inc_ret") == 33)
    t.step()

    // the enabled signal should only inhibit updating state, the method should still work, even if enabled is false
    t.poke("inc_enabled", 0)
    t.poke("inc_arg", 64)
    assert(t.peek("inc_ret") == 65)
    t.step()
  }

  "an UntimedModule with state" should "be elaborated with UntimedModule(new ...)" in {
    val m = UntimedModule(new Counter4Bit)
    assert(m.isElaborated)
    assert(m.name == "Counter4Bit")
    assert(m.methods.size == 1)
    assert(m.value.getWidth == 4)
    val inc = m.methods.head
    assert(inc.name == "inc")

    // the state update should be guarded
    val src = m.getFirrtl.circuit.serialize
    assert(src.contains("mux(inc_enabled"))
  }

  "an UntimedModule with a sub module" should "be elaborated with UntimedModule(new ...)" in {
    val m = UntimedModule(new Counter4BitWithSubModule)
    assert(m.isElaborated)
    assert(m.name == "Counter4BitWithSubModule")
    assert(m.methods.size == 1)
    assert(m.value.getWidth == 4)
    val inc = m.methods.head
    assert(inc.name == "inc")
  }

  "an UntimedModule with a state-less sub module" should "be elaborated with UntimedModule(new ...)" in {
    val m = UntimedModule(new Counter4BitWithSubModuleAndTwoCallsNoSubstate)
    assert(m.isElaborated)
    assert(m.name == "Counter4BitWithSubModuleAndTwoCallsNoSubstate")
    assert(m.methods.size == 1)
    assert(m.value.getWidth == 4)
    val inc = m.methods.head
    assert(inc.name == "inc")
  }

}
