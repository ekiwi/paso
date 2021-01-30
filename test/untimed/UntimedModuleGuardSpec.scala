package untimed

import chisel3._
import org.scalatest.flatspec.AnyFlatSpec
import paso.UntimedModule



class UntimedTwoGuardedCounter extends UntimedModule {
  val count = RegInit(0.U(32.W))
  // two guards are allowed and will be combined
  val inc = fun("inc").in(UInt(32.W)).when(count < 4.U) { in =>
    count := count + in
  }
}


class UntimedModuleGuardSpec extends AnyFlatSpec {
  "a untimed module" should "be allowed to have a guard" in {
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

    // now we should be forbidden to increment since count < 4.U is false (since count=4)
    assert(dut.peek("inc_guard") == 0)
  }

}
