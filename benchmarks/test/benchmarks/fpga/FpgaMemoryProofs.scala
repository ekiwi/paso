package benchmarks.fpga

import org.scalatest.flatspec.AnyFlatSpec
import paso._
import chisel3._

class FpgaMemoryProofs extends AnyFlatSpec with PasoTester {
  "SimulationMemory with 1 Read, 1 Write Port" should "pass bmc" in {
    val data = MemData(MemSize(UInt(32.W), 32), 1, 1)
    test(new SimulationMem(data))(new Mem1W1RProtocol(_)).bmc(4)
  }

  "SimulationMemory with 1 Read, 1 Write Port" should "refine its spec" in {
    val data = MemData(MemSize(UInt(32.W), 32), 1, 1)
    test(new SimulationMem(data))(new Mem1W1RProtocol(_)).proof(Paso.MCZ3, new ProofCollateral(_, _){
      mapping { (impl, spec) =>
        forall(0 until impl.d.size.depth.toInt){ ii =>
          when(spec.valid(ii)) { assert(spec.mem(ii) === impl.mem(ii)) }
        }
      }
    })
  }

  "Charles Eric LaForest LVT 2W4R memory" should "refine its spec" in {
    val data = MemData(MemSize(UInt(32.W), 32), 4, 2)
    type ImplMem = LVTMemory[ParallelWriteMem[SimulationMem], SimulationMem]
    def makeBanked(data: MemData) = new ParallelWriteMem(data, new SimulationMem(_))
    def makeLVTMem(data: MemData) = new LVTMemory(data, makeBanked, new SimulationMem(_))
    test(makeLVTMem(data))(new Mem2W4RProtocol(_)).proof(Paso.MCZ3, new LaForest2W4RInductive(_, _))
  }

  "Charles Eric LaForest LVT 2W4R memory" should "pass bmc" in {
    val data = MemData(MemSize(UInt(32.W), 32), 4, 2)
    type ImplMem = LVTMemory[ParallelWriteMem[SimulationMem], SimulationMem]
    def makeBanked(data: MemData) = new ParallelWriteMem(data, new SimulationMem(_))
    def makeLVTMem(data: MemData) = new LVTMemory(data, makeBanked, new SimulationMem(_))
    test(makeLVTMem(data))(new Mem2W4RProtocol(_)).bmc(Paso.MCZ3, 10)
  }

  // TODO: while we believe that the memory should be correct, we are missing the correct invariant
  "Charles Eric LaForest XOR 2W4R memory" should "refine its spec" ignore {
    val data = MemData(MemSize(UInt(32.W), 32), 4, 2)
    type ImplMem = XorMemory[ParallelWriteMem[SimulationMem]]
    def makeBanked(data: MemData) = new ParallelWriteMem(data, new SimulationMem(_))
    def makeXorMem(data: MemData) = new XorMemory(data, makeBanked)
    test(makeXorMem(data))(new Mem2W4RProtocol(_)).proof(Paso.MCZ3, new LaForest2W4RXorInductive(_, _))
  }

  "Charles Eric LaForest XOR 2W4R memory" should "pass BMC" in {
    val data = MemData(MemSize(UInt(32.W), 32), 4, 2)
    type ImplMem = XorMemory[ParallelWriteMem[SimulationMem]]
    def makeBanked(data: MemData) = new ParallelWriteMem(data, new SimulationMem(_))
    def makeXorMem(data: MemData) = new XorMemory(data, makeBanked)

    test(makeXorMem(data))(new Mem2W4RProtocol(_)).bmc(4)
  }

  "SimulationMemory with 4 Read, 3 Write Port" should "refine its spec" in {
    val data = MemData(MemSize(UInt(32.W), 32), 4, 2)
    test(new SimulationMem(data))(new Mem2W4RProtocol(_)).proof(Paso.MCCVC4, new ProofCollateral(_, _){
      mapping { (impl, spec) =>
        forall(0 until impl.d.size.depth.toInt){ ii =>
          when(spec.valid(ii)) { assert(spec.mem(ii) === impl.mem(ii)) }
        }
      }
    })
  }
}
