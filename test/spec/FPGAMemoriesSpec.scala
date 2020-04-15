// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package spec

import chisel3._
import chisel3.util._
import impl.{FPGAMem, MemData, MemSize, SimulationMem}
import paso._
import org.scalatest._
import paso.chisel.Elaboration
import paso.verification.VerificationProblem


class In(val depth: BigInt, val w: Int) extends Bundle {
  val readAddr = UInt(log2Ceil(depth).W)
  val writeAddr = UInt(log2Ceil(depth).W)
  val writeData = UInt(w.W)
}
class Untimed1W1RMemory(size: MemSize) extends UntimedModule {
  val mem = Mem(size.depth, size.dataType)
  val valid = Mem(size.depth, Bool())
  val rw = fun("rw").in(new In(size.depth, size.dataType.getWidth)).out(size.dataType) { (in, readData) =>
    when(valid(in.readAddr)) {
      when(in.readAddr === in.writeAddr) {
        readData := in.writeData
      } .otherwise {
        readData := mem(in.readAddr)
      }
    } .otherwise {
      readData := DontCare
    }
    mem(in.writeAddr) := in.writeData
    valid(in.writeAddr) := true.B
  }
}

class Mem1W1RProtocol[F <: FPGAMem](impl: F, spec: Untimed1W1RMemory) extends Binding(impl, spec) {
  protocol(spec.rw)(impl.io) { (clock, dut, in, readData) =>
    dut.write.head.addr.poke(in.writeAddr)
    dut.write.head.data.poke(in.writeData)
    dut.read.head.addr.poke(in.readAddr)
    clock.step()
    dut.read.head.data.expect(readData)
    clock.step()
  }
}

class Simulation1W1RInductive(impl: SimulationMem, spec: Untimed1W1RMemory) extends Mem1W1RProtocol(impl, spec) {
  mapping { (impl, spec) =>
    forall(0 until impl.d.size.depth.toInt){ ii =>
      when(spec.valid(ii)) { assert(spec.mem(ii) === impl.mem(ii)) }
    }
  }
}

class FPGAMemoriesSpec extends FlatSpec {
  "SimulationMemory with 1 Read, 1 Write Port" should "refine its spec" in {
    val data = MemData(MemSize(UInt(32.W), 32), 1, 1)
    val p = Elaboration()[SimulationMem, Untimed1W1RMemory](new SimulationMem(data), new Untimed1W1RMemory(data.size), (impl, spec) => new Simulation1W1RInductive(impl, spec))
    VerificationProblem.verify(p)
  }
}
