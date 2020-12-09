// Copyright 2020, SiFive, Inc
// released under Apache License Version 2.0
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package untimed

import chisel3._
import org.scalatest.flatspec.AnyFlatSpec
import paso.UntimedModule
import paso.untimed.UntimedError

class Counter4BitWithSubModuleAndTwoCalls extends UntimedModule {
  val value = RegInit(0.U(4.W))
  val ii = UntimedModule(new UntimedInc)
  val inc = fun("inc").out(UInt(4.W)) { out =>
    // calling a method of a stateful submodule twice is forbidden (even if the method itself is pure)
    value := ii.inc(value)
    out := ii.inc(value)
  }
}

class RegInMethodModule extends UntimedModule {
  val thisIsOK = RegInit(0.U(3.W))

  val foo = fun("foo") {
    // registers may not be declared inside of methods!
    val thisIsNot = RegInit(0.U(3.W))
  }
}

// recursion is always forbidden
class RecursionModule extends UntimedModule {
  val foo: paso.untimed.OMethod[UInt] = fun("foo").out(UInt(32.W)) { o =>
    o := foo()
  }
}

// we currently do not support method calling other methods in the same module,
// this feature would be possible to support, just needs a some engineering work
class InternalMethodCallModule extends UntimedModule {
  val bar = fun("bar").out(UInt(32.W)) { o => o := 1234.U }
  val foo = fun("foo").out(UInt(32.W)) { o => o := bar() }
}

// SyncReadMem should never be used since we require all outputs of a transaction to be
// combinatorial, i.e. "instantaneously" available without a clock transition.
// A SyncReadMem would incur a read latency of 1.
class SyncReadMemModule extends UntimedModule {
  val mem = SyncReadMem(32, UInt(8.W))
}

class UntimedModuleExceptionSpec extends AnyFlatSpec {
  "declaring a register inside a method" should "lead to an exception" in {
    val err = intercept[UntimedError] {
      UntimedModule(new RegInMethodModule).getFirrtl
    }
    assert(err.getMessage.contains("create a register"))
    assert(err.getMessage.contains("in method foo of RegInMethodModule"))
  }

  "calling a method of a stateful submodule more than once" should "lead to an exception" in {
    val err = intercept[UntimedError] {
      UntimedModule(new Counter4BitWithSubModuleAndTwoCalls).getFirrtl
    }
    assert(err.getMessage.contains("[Counter4BitWithSubModuleAndTwoCalls.inc] cannot call more than one method of stateful submodule UntimedInc"))
  }

  "recursive method calls" should "lead to an exception" in {
    val err = intercept[UntimedError] {
      UntimedModule(new RecursionModule).getFirrtl
    }
    assert(err.getMessage.contains("recursive calls are not allowed"))
  }

  "calls to methods in the same module" should "lead to an exception" in {
    val err = intercept[UntimedError] {
      UntimedModule(new InternalMethodCallModule).getFirrtl
    }
    assert(err.getMessage.contains("currently, only calls to submodules are supported"))
  }

  "creating a SyncReadMem" should "lead to an exception" in {
    val err = intercept[UntimedError] {
      UntimedModule(new SyncReadMemModule).getFirrtl
    }
    assert(err.getMessage.contains("need to use a combinatorial Mem instead"))
  }
}
