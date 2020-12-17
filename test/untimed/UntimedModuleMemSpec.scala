// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package untimed

import chisel3._
import org.scalatest.flatspec.AnyFlatSpec
import paso.UntimedModule
import paso.untimed.UntimedError


class UntimedMem extends UntimedModule {
  val mem = Mem(32, UInt(32.W))
  val read = fun("read").in(UInt(5.W)).out(UInt(32.W)) { (in, out) =>
    out := mem.read(in)
  }
  val write = fun("write").in(new WriteIO) { in =>
    mem.write(in.addr, in.data)
  }
}

class WriteIO extends Bundle {
  val addr = UInt(5.W)
  val data = UInt(32.W)
}

class UntimedModuleMemSpec extends AnyFlatSpec {
  behavior of "Memories in Untimed Modules"

  // this is testing for bug where the memory would be written ot regardless of whether the transaction was enabled or not
  it should "only write when transaction is enabled" in {
    // elaborate module and get tester interface
    val m = UntimedModule(new UntimedMem).getTester

    // disable both transactions by default
    m.poke("read_enabled", 0)
    m.poke("write_enabled", 0)

    // read out the memory, every entry should be zero
    // NOTE: since read does not update any state, the value of "read_enabled" should not matter
    (0 until 32).foreach{ ii => m.poke("read_arg", ii) ; assert(m.peek("read_ret") == 0) }

    // now we apply a write address and write value =/= 0, with write_enabled set to 1
    // ==> this should result in a change of the memory in that location
    m.poke("write_enabled", 1)
    m.poke("write_arg_addr", 31)
    m.poke("write_arg_data", 12345)
    m.step()

    (0 until 31).foreach{ ii => m.poke("read_arg", ii) ; assert(m.peek("read_ret") == 0) }
    m.poke("read_arg", 31)
    assert(m.peek("read_ret") == 12345)

    // if we have write_enabled set to 0, the values in memory should not change
    m.poke("write_enabled", 0)
    m.poke("write_arg_addr", 31)
    m.poke("write_arg_data", 54321)
    m.step()

    (0 until 31).foreach{ ii => m.poke("read_arg", ii) ; assert(m.peek("read_ret") == 0) }
    m.poke("read_arg", 31)
    assert(m.peek("read_ret") == 12345)

    // if we have write_enabled set to 1 and also read_enabled set to 1, the values in memory should not change
    m.poke("write_enabled", 1)
    m.poke("read_enabled", 1)
    m.poke("write_arg_addr", 31)
    m.poke("write_arg_data", 54321)
    m.step()

    (0 until 31).foreach{ ii => m.poke("read_arg", ii) ; assert(m.peek("read_ret") == 0) }
    m.poke("read_arg", 31)
    assert(m.peek("read_ret") == 12345)
  }
}
