package untimed

import chisel3._
import org.scalatest.flatspec.AnyFlatSpec
import paso.UntimedModule



class UntimedTwoGuardedCounter extends UntimedModule {
  val count = RegInit(0.U(32.W))
  // two guards are allowed and will be combined
  val inc = fun("inc").in(UInt(32.W)).when(count < 5.U).when(count < 4.U) { in =>
    count := count + in
  }
}

class UntimedGuardedInputCounter extends UntimedModule {
  val count = RegInit(0.U(32.W))
  // we can add guards not only on the state, but also over the inputs
  val inc = fun("inc").in(UInt(32.W)).when(count < 5.U).when(in => (count + in) <= 4.U) { in =>
    count := count + in
  }
}

class UntimedModuleGuardSpec extends AnyFlatSpec {
  "a untimed module" should "be allowed to have more than one guard" in {
    val dut = UntimedModule(new UntimedTwoGuardedCounter).getTester

    // at the beginning the count = 0 => we should be allowed to increment
    assert(dut.peek("inc_guard") == 1)

    // increment by three
    dut.poke("inc_enabled", 1)
    dut.poke("inc_arg", 3)
    assert(dut.peek("inc_guard") == 1)
    dut.step()

    // now we should still be able to increment
    assert(dut.peek("inc_guard") == 1)

    // increment by one
    dut.poke("inc_enabled", 1)
    dut.poke("inc_arg", 1)
    assert(dut.peek("inc_guard") == 1)
    dut.step()

    // now we should be forbidden to increment since while count < 5.U is true, count < 4.U is false (since count=4)
    assert(dut.peek("inc_guard") == 0)
  }

  "a untimed module" should "be allowed to specify a guard over inputs" in {
    val dut = UntimedModule(new UntimedGuardedInputCounter).getTester

    // increment by three
    dut.poke("inc_enabled", 1)
    dut.poke("inc_arg", 3)
    assert(dut.peek("inc_guard") == 1)
    dut.step()

    // now we should still be able to increment by one
    dut.poke("inc_arg", 1)
    assert(dut.peek("inc_guard") == 1)

    // however incrementing mby more should be forbidden
    dut.poke("inc_arg", 2)
    assert(dut.peek("inc_guard") == 0)

    // the guard should be independent of whether the method is enable or not
    dut.poke("inc_enabled", 0)
    dut.poke("inc_arg", 1)
    assert(dut.peek("inc_guard") == 1)
    dut.poke("inc_arg", 2)
    assert(dut.peek("inc_guard") == 0)
  }

}
