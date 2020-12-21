// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

// Chisel implementations of various multiported FPGA memories
// as described by Charles Eric LaForest, University of Toronto.
// see: http://fpgacpu.ca/multiport/ and http://fpgacpu.ca/multiport/Multiported-Memory-Example-Code/

package benchmarks.fpga

import chisel3._
import chisel3.experimental.{ChiselAnnotation, annotate}
import chisel3.util._
import firrtl.annotations.MemoryScalarInitAnnotation

case class MemSize(dataType: UInt, depth: BigInt) { def addrType: UInt = UInt(log2Ceil(depth).W) }
case class MemData(size: MemSize, readPorts: Int, writePorts: Int, zeroInit: Boolean = false) {
  require(readPorts > 0)
  require(writePorts > 0)
}
class ReadPort(val d: MemSize) extends Bundle {
  val addr = Input(d.addrType)
  val data = Output(d.dataType)
}
class WritePort(val d: MemSize) extends Bundle {
  val addr = Input(d.addrType)
  val data = Input(d.dataType)
}
class MemoryIO(val d: MemData) extends Bundle {
  val read =  Vec(d.readPorts, new ReadPort(d.size))   //(0 until d.readPorts).map{ _ => new ReadPort(d.size) }
  val write = Vec(d.writePorts, new WritePort(d.size)) //(0 until d.writePorts).map{ _ => new WritePort(d.size) }
}
abstract class FPGAMem extends Module { val io: MemoryIO ; def d: MemData = io.d }

/** multiple read ports through banking */
class ParallelWriteMem[B <: FPGAMem](data: MemData, base: MemData => B) extends FPGAMem {
  require(data.readPorts > 0 && data.readPorts <= 32)
  val bankData = data.copy(readPorts = 1)
  val banks = (0 until data.readPorts).map{ _ => Module(base(bankData)) }
  val io = IO(new MemoryIO(data))

  // connect write ports
  banks.foreach(m => m.io.write.zip(io.write).foreach{case (a,b) => a <> b})
  // connect read ports
  val mod_read_ports = banks.flatMap(_.io.read)
  mod_read_ports.zip(io.read).foreach{case (a,b) => a <> b}
}

/** Live-Value-Table based memory
 *  see: http://fpgacpu.ca/multiport/FPGA2010-LaForest-Paper.pdf
 * */
class LVTMemory[B <: FPGAMem, L <: FPGAMem](data: MemData, base: MemData => B, makeLvt: MemData => L) extends FPGAMem {
  val bankData = data.copy(writePorts = 1)
  val factor = data.writePorts
  val banks = (0 until factor).map{ _ => Module(base(bankData)) }
  val io = IO(new MemoryIO(data))

  // create the live-value table
  val lvtSize = MemSize(UInt(log2Ceil(factor).W), data.size.depth)
  val lvt = Module(makeLvt(d.copy(size=lvtSize)))

  // remember addr -> bank mapping
  io.write.zip(lvt.io.write).zipWithIndex.foreach { case ((writeIn, lvtWrite), ii) =>
    lvtWrite.addr := writeIn.addr
    lvtWrite.data := ii.U
  }

  // connect write ports to banks
  val mod_write_ports = banks.flatMap(_.io.write)
  mod_write_ports.zip(io.write).foreach{case (a,b) => a <> b}

  // retrieve values from correct bank
  io.read.zip(lvt.io.read).zipWithIndex.foreach { case ((readOut, lvtRead), ii) =>
    lvtRead.addr := readOut.addr
    readOut.data := MuxLookup(lvtRead.data.asUInt(), DontCare, banks.zipWithIndex.map{case (m, jj) => jj.U -> m.io.read(ii).data })
    banks.foreach{ _.io.read(ii).addr := readOut.addr }
  }
}

/**
 * XOR based multi-port memory.
 * see: http://fpgacpu.ca/multiport/TRETS2014-LaForest-Article.pdf
 */
class XorMemory[B <: FPGAMem](data: MemData, base: MemData => B) extends FPGAMem {
  val readPortsPerBank = data.writePorts - 1 + data.readPorts
  val banks = (0 until data.writePorts).map{_ => Module(base(MemData(data.size, readPortsPerBank, 1, zeroInit = true)))}
  val io = IO(new MemoryIO(data))

  // delay write ports (this is necessary because reading takes one cycle and is required for the xor to work)
  val writeDelayed = io.write.zipWithIndex.map{ case(w,ii) =>
    (RegNext(w.data).suggestName(s"w${ii}_delay_data"), RegNext(w.addr).suggestName(s"w${ii}_delay_addr"))
  }

  // connect banks to write ports
  banks.zip(io.write).zip(writeDelayed).zipWithIndex.foreach { case (((targetBank, write), delayed), ii) =>
    // find the corresponding read ports on all other banks
    val others = banks.zipWithIndex.flatMap{ case(otherBank, jj) =>
      if(jj == ii) None
      else if(jj < ii) Some(otherBank.io.read(jj))
      else Some(otherBank.io.read(jj-1))
    }
    // connect read port addresses to latest write address
    others.foreach(r => r.addr := write.addr)

    // in the next cycle: xor new and all old values
    val data = (Seq(delayed._1) ++ others.map(_.data)).reduce((a,b) => a ^ b)
    targetBank.io.write(0).addr := delayed._2
    targetBank.io.write(0).data := data
  }

  // connect banks to read ports
  val readPortOffset = data.writePorts - 1
  io.read.zipWithIndex.foreach { case (read, ii) =>
    // read from all banks
    banks.foreach(b => b.io.read(readPortOffset + ii).addr := read.addr)
    val values = banks.map(b => b.io.read(readPortOffset + ii).data)

    // return xor
    val data = values.reduce((a,b) => a ^ b)
    // bypass for the case when the read address is equal to the write address
    val bypasses = writeDelayed.zip(io.write).zipWithIndex.map {
      case (((delayedData, _), write), jj) =>
        val doBypass =  RegNext(write.addr === read.addr).suggestName(s"w${jj}_addr_eq_r${ii}_addr")
        doBypass -> delayedData
    }
    read.data := MuxCase(data, bypasses)
  }
}

class SimulationMem(data: MemData) extends FPGAMem {
  val io = IO(new MemoryIO(data))
  val mem = SyncReadMem(data.size.depth, data.size.dataType, SyncReadMem.WriteFirst)
  io.read.foreach(r => r.data := mem.read(r.addr))
  io.write.foreach(w => mem.write(w.addr, w.data))
  if(data.zeroInit) {
    annotate(new ChiselAnnotation {
      override def toFirrtl = MemoryScalarInitAnnotation(mem.toAbsoluteTarget, 0)
    })

  }
}

object FPGAMemories {
}

