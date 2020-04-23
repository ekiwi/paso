// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package spec

import chisel3._
import chisel3.util._
import impl.{FPGAMem, LVTMemory, MemData, MemSize, ParallelWriteMem, SimulationMem, XorMemory}
import paso._
import org.scalatest._
import paso.chisel.Elaboration
import paso.verification.VerificationProblem

// NOTE: while the spec is currently hard coded for a certain number of read and write ports, one
//       could write a spec generator that takes these numbers as inputs and generates the correct spec.

/////////////////////////////// 1W 1R ///////////////////////
/**
 * A memory with one read and one write port.
 * - A read/write conflict returns the new value (other options would be to return the old value or an undefined result)
 * - Reading from a location that has not been written to results in an undefined (arbitrary) result.
 *  */
class Untimed1W1RMemory(size: MemSize) extends UntimedModule {
  val mem = Mem(size.depth, size.dataType)
  val valid = Mem(size.depth, Bool())
  class In(val depth: BigInt, val w: Int) extends Bundle {
    val readAddr = UInt(log2Ceil(depth).W)
    val writeAddr = UInt(log2Ceil(depth).W)
    val writeData = UInt(w.W)
  }
  val rw = fun("rw").in(new In(size.depth, size.dataType.getWidth)).out(size.dataType) { (in, readData) =>
    when(in.readAddr === in.writeAddr) {
      readData := in.writeData
    } .elsewhen(valid(in.readAddr)) {
      readData := mem(in.readAddr)
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
    dut.write.head.addr.poke(DontCare)
    dut.write.head.data.poke(DontCare)
    dut.read.head.addr.poke(DontCare)
    dut.read.head.data.expect(readData)
  }
}

class Simulation1W1RInductive(impl: SimulationMem, spec: Untimed1W1RMemory) extends Mem1W1RProtocol(impl, spec) {
  mapping { (impl, spec) =>
    forall(0 until impl.d.size.depth.toInt){ ii =>
      when(spec.valid(ii)) { assert(spec.mem(ii) === impl.mem(ii)) }
    }
  }
}

/////////////////////////////// 2W 4R ///////////////////////

/**
 * A memory with four read and two write ports.
 * - A read/write conflict returns the new value (other options would be to return the old value or an undefined result)
 * - Reading from a location that has not been written to results in an undefined (arbitrary) result.
 * - A write/write conflict results in an undefined (arbitrary) value being written to the location.
 *  */
class Untimed2W4RMemory(size: MemSize) extends UntimedModule {
  val mem = Mem(size.depth, size.dataType)
  val valid = Mem(size.depth, Bool())
  class In(val addrWidth: Int, val dataWidth: Int) extends Bundle {
    val readAddr0 = UInt(addrWidth.W)
    val readAddr1 = UInt(addrWidth.W)
    val readAddr2 = UInt(addrWidth.W)
    val readAddr3 = UInt(addrWidth.W)
    val writeAddr0 = UInt(addrWidth.W)
    val writeData0 = UInt(dataWidth.W)
    val writeAddr1 = UInt(addrWidth.W)
    val writeData1 = UInt(dataWidth.W)
  }
  class Out(val dataWidth: Int) extends Bundle {
    val readData0 = UInt(dataWidth.W)
    val readData1 = UInt(dataWidth.W)
    val readData2 = UInt(dataWidth.W)
    val readData3 = UInt(dataWidth.W)
  }

  def read(addr: UInt, data: UInt, in: In): Unit = {
    when(addr === in.writeAddr0) {
      // if there is a write-write collision, the result is undefined
      when(in.writeAddr0 === in.writeAddr1) {
        data := DontCare
      } .otherwise {
        data := in.writeData0
      }
    } .elsewhen(addr === in.writeAddr1) {
      data := in.writeData1
    } .elsewhen(valid(addr)) {
      data := mem(addr)
    } .otherwise {
      data := DontCare
    }
  }

  val rw = fun("rw").in(new In(log2Ceil(size.depth), size.dataType.getWidth)).out(new Out(size.dataType.getWidth)) { (in, out) =>
    // read
    read(in.readAddr0, out.readData0, in)
    read(in.readAddr1, out.readData1, in)
    read(in.readAddr2, out.readData2, in)
    read(in.readAddr3, out.readData3, in)

    // write
    when(in.writeAddr0 === in.writeAddr1) {
      valid(in.writeAddr0) := false.B
    } .otherwise {
      mem(in.writeAddr0) := in.writeData0
      valid(in.writeAddr0) := true.B
      mem(in.writeAddr1) := in.writeData1
      valid(in.writeAddr1) := true.B
    }
  }
}

// While the protocol does not depend on the implementation, it does depend on the number of read and write ports.
// We could turn the protocol into a generator and make it generic vis-a-vis the number of ports.
class Mem2W4RProtocol[F <: FPGAMem](impl: F, spec: Untimed2W4RMemory) extends Binding(impl, spec) {
  protocol(spec.rw)(impl.io) { (clock, dut, in, out) =>
    // write
    dut.write(0).addr.poke(in.writeAddr0)
    dut.write(0).data.poke(in.writeData0)
    dut.write(1).addr.poke(in.writeAddr1)
    dut.write(1).data.poke(in.writeData1)
    //read
    dut.read(0).addr.poke(in.readAddr0)
    dut.read(1).addr.poke(in.readAddr1)
    dut.read(2).addr.poke(in.readAddr2)
    dut.read(3).addr.poke(in.readAddr3)

    clock.step()

    // invalidate inputs (TODO: add option to make pokes not stick!)
    dut.write(0).addr.poke(DontCare)
    dut.write(0).data.poke(DontCare)
    dut.write(1).addr.poke(DontCare)
    dut.write(1).data.poke(DontCare)
    dut.read(0).addr.poke(DontCare)
    dut.read(1).addr.poke(DontCare)
    dut.read(2).addr.poke(DontCare)
    dut.read(3).addr.poke(DontCare)

    // verify read data
    dut.read(0).data.expect(out.readData0)
    dut.read(1).data.expect(out.readData1)
    dut.read(2).data.expect(out.readData2)
    dut.read(3).data.expect(out.readData3)
  }
}

class LaForest2W4RInductive(impl: LVTMemory[ParallelWriteMem[SimulationMem], SimulationMem],
                            spec: Untimed2W4RMemory) extends Mem2W4RProtocol(impl, spec) {
  require(impl.d.writePorts == 2)
  require(impl.d.readPorts == 4)

  mapping { (impl, spec) =>
    forall(0 until impl.d.size.depth.toInt){ addr =>
      when(spec.valid(addr)) {
        // write banks
        (0 until 2).foreach { bank =>
          when(impl.lvt.mem(addr) === bank.U) {
            // read banks
            assert(spec.mem(addr) === impl.banks(bank).banks(0).mem(addr))
            assert(spec.mem(addr) === impl.banks(bank).banks(1).mem(addr))
            assert(spec.mem(addr) === impl.banks(bank).banks(2).mem(addr))
            assert(spec.mem(addr) === impl.banks(bank).banks(3).mem(addr))
          }
        }
      }
    }
  }
}

class LaForest2W4RXorInductive(impl: XorMemory[ParallelWriteMem[SimulationMem]],
                               spec: Untimed2W4RMemory) extends Mem2W4RProtocol(impl, spec) {
  require(impl.d.writePorts == 2)
  require(impl.d.readPorts == 4)

  mapping { (impl, spec) =>
    forall(0 until impl.d.size.depth.toInt){ addr =>
      when(spec.valid(addr)) {
        // if the address was recently written, the data is still in flight
        when(addr === impl.writeDelayed(0)._2) {
          assert(spec.mem(addr) === impl.writeDelayed(0)._1)
        } .elsewhen(addr === impl.writeDelayed(1)._2) {
          assert(spec.mem(addr) === impl.writeDelayed(1)._1)
        } .otherwise {
          val data = impl.banks.map(_.banks(0).mem(addr)).reduce((a, b) => a ^ b)
          assert(spec.mem(addr) === data)
          // all read banks in a write bank have the same value
          (0 until 2).foreach { writeBank =>
            val value = impl.banks(writeBank).banks(0).mem(addr)
            (1 until impl.readPortsPerBank).foreach { readBank =>
              assert(impl.banks(writeBank).banks(readBank).mem(addr) === value)
            }
          }
        }
      }
    }
  }
}


class Simulation2W4RInductive(impl: SimulationMem, spec: Untimed2W4RMemory) extends Mem2W4RProtocol(impl, spec) {
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

  "Charles Eric LaForest LVT 2W4R memory" should "refine its spec" in {
    val data = MemData(MemSize(UInt(32.W), 32), 4, 2)
    type ImplMem = LVTMemory[ParallelWriteMem[SimulationMem], SimulationMem]
    def makeSimMem1W1R(size: MemSize) = new SimulationMem(MemData(size, 1, 1))
    def makeSimMem(data: MemData) = new SimulationMem(data)
    def makeBanked(size: MemSize) = new ParallelWriteMem(size, makeSimMem1W1R, data.readPorts)
    def makeLVTMem(size: MemSize) = new LVTMemory(size, makeBanked, makeSimMem, data.writePorts)
    val p = Elaboration()[ImplMem, Untimed2W4RMemory](makeLVTMem(data.size), new Untimed2W4RMemory(data.size), (impl, spec) => new LaForest2W4RInductive(impl, spec))
    VerificationProblem.verify(p)
  }

  "Charles Eric LaForest XOR 2W4R memory" should "refine its spec" in {
    val data = MemData(MemSize(UInt(32.W), 32), 4, 2)
    type ImplMem = XorMemory[ParallelWriteMem[SimulationMem]]
    def makeSimMem1W1R(size: MemSize) = new SimulationMem(MemData(size, 1, 1))
    def makeBanked(data: MemData) = new ParallelWriteMem(data.size, makeSimMem1W1R, data.readPorts)
    def makeXorMem(data: MemData) = new XorMemory(data, makeBanked)
    val p = Elaboration()[ImplMem, Untimed2W4RMemory](makeXorMem(data), new Untimed2W4RMemory(data.size), (impl, spec) => new LaForest2W4RXorInductive(impl, spec))
    VerificationProblem.verify(p)
  }

  "SimulationMemory with 4 Read, 3 Write Port" should "refine its spec" in {
    val data = MemData(MemSize(UInt(32.W), 32), 4, 2)
    val p = Elaboration()[SimulationMem, Untimed2W4RMemory](new SimulationMem(data), new Untimed2W4RMemory(data.size), (impl, spec) => new Simulation2W4RInductive(impl, spec))
    VerificationProblem.verify(p)
  }
}
