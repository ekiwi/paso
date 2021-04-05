// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.invariants

import org.scalatest.flatspec.AnyFlatSpec
import chisel3._
import chisel3.experimental.{ChiselAnnotation, annotate}
import firrtl.annotations.MemoryScalarInitAnnotation
import paso._

trait HasIO[D <: Data] extends RawModule { val io: D }

class MemIO extends Bundle {
  val addr = Input(UInt(5.W))
  val readData = Output(UInt(32.W))
  val writeData = Input(UInt(32.W))
  val writeEnable = Input(Bool())
}

// simple memory wrapper to serve as an example
class ChiselMem extends Module with HasIO[MemIO] {
  val io = IO(new MemIO)

  val mem = SyncReadMem(32, UInt(32.W), SyncReadMem.Undefined)
  annotate(new ChiselAnnotation {
    override def toFirrtl = MemoryScalarInitAnnotation(mem.toAbsoluteTarget, 0)
  })

  val addr = io.addr
  val doWrite = io.writeEnable && !reset.asBool()
  io.readData := mem.read(addr)
  when(doWrite) { mem.write(addr, io.writeData) }
}

// wrapper class to test referring to state in a submodule
class ChiselMemWrapper extends Module with HasIO[MemIO] {
  val io = IO(new MemIO)
  val sub = Module(new ChiselMem)
  io <> sub.io
}

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

class MemProtocol[M <: HasIO[MemIO]](impl: M) extends ProtocolSpec[UntimedMem] {
  val spec = new UntimedMem

  protocol(spec.read)(impl.io) { (clock, dut, addr, data) =>
    dut.writeEnable.poke(false.B)
    dut.addr.poke(addr)
    clock.stepAndFork()
    dut.writeEnable.poke(DontCare)
    dut.addr.poke(DontCare)
    dut.readData.expect(data)
    clock.step()
  }

  protocol(spec.write)(impl.io) { (clock, dut, in) =>
    dut.writeEnable.poke(true.B)
    dut.addr.poke(in.addr)
    dut.writeData.poke(in.data)
    clock.step()
  }
}

class MemProof(impl: ChiselMem, spec: UntimedMem) extends ProofCollateral(impl, spec) {
  mapping { (impl, spec) =>
    forall(0 until 32) { ii =>
      assert(impl.mem.read(ii) === spec.mem.read(ii))
    }
  }
}

class MemProofWithExtensionality(impl: ChiselMem, spec: UntimedMem) extends ProofCollateral(impl, spec) {
  mapping { (impl, spec) =>
    assert(impl.mem === spec.mem)
  }
}

class MemWrapperProof(impl: ChiselMemWrapper, spec: UntimedMem) extends ProofCollateral(impl, spec) {
  mapping { (impl, spec) =>
    forall(0 until 32) { ii =>
      assert(impl.sub.mem.read(ii) === spec.mem.read(ii))
    }
  }
}


class MemInvariantSpec extends AnyFlatSpec with PasoTester {
  behavior of "Paso invariants"

  // small sanity check
  it should "work for bmc ...." in { test(new ChiselMem)(new MemProtocol(_)).bmc(5) }
  it should "work for random ...." in { test(new ChiselMem)(new MemProtocol(_)).randomTest(5) }

  it should "be able to use memory equality" in {
    test(new ChiselMem)(new MemProtocol(_)).proof(Paso.MCZ3, new MemProofWithExtensionality(_, _))
  }

  it should "be able to refer to a memory" in {
    test(new ChiselMem)(new MemProtocol(_)).proof(Paso.MCZ3, new MemProof(_, _))
  }

  it should "be able to refer to a memory in a submodule" in {
    test(new ChiselMemWrapper)(new MemProtocol(_)).proof(Paso.MCZ3, new MemWrapperProof(_, _))
  }
}
