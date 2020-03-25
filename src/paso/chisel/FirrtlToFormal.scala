// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

// this takes advantage of yosys in order to convert a firrtl module to a symbolic transition system
// the process is:
// Chirrtl --- firrtl compiler ---> Verilog --- yosys ---> btor2 --- uclid btor2 parser ---> SymbolicTransitionSystem
// TODO: cut out the yosys part...


import java.io.{File, PrintWriter}

import uclid.smt
import firrtl.annotations.Annotation
import firrtl.{ChirrtlForm, CircuitState, Compiler, HighForm, LowForm, MinimumLowFirrtlOptimization, Transform, VerilogEmitter, ir}
import firrtl.CompilerUtils.getLoweringTransforms
import firrtl.transforms.{BlackBoxSourceHelper, NoDCEAnnotation}
import firrtl.util.BackendCompilationUtilities

import scala.sys.process._


class MinimumFirrtlToVerilogCompiler extends Compiler {
  def emitter = new VerilogEmitter
  def transforms: Seq[Transform] = getLoweringTransforms(HighForm, LowForm) ++
      Seq(new MinimumLowFirrtlOptimization, new BlackBoxSourceHelper)
}

object FirrtlToFormal extends BackendCompilationUtilities {
  private val compiler = new MinimumFirrtlToVerilogCompiler

  private def makeVerilog(testDir: File, circuit: ir.Circuit, annos: Seq[Annotation]): String = {
    val state = CircuitState(circuit, ChirrtlForm, Seq(NoDCEAnnotation))
    val verilog = compiler.compileAndEmit(state)
    val file = new PrintWriter(s"${testDir.getAbsolutePath}/${circuit.main}.v")
    file.write(verilog.getEmittedCircuit.value)
    file.close()
    circuit.main
  }

  private def makeBtor(testDir: File, module: String): (Boolean, String) = {
    val scriptFileName = s"${testDir.getAbsolutePath}/yosys_script"
    val btorFileName = s"${testDir.getAbsolutePath}/$module.btor2"
    val yosysScriptWriter = new PrintWriter(scriptFileName)
    yosysScriptWriter.write(
      s"""read_verilog -sv -defer ${testDir.getAbsolutePath}/$module.v
         |prep -nordff -top $module
         |flatten
         |setattr -unset keep
         |write_btor -v ${testDir.getAbsolutePath}/$module.btor2
         |"""
          .stripMargin)
    yosysScriptWriter.close()

    // execute yosys
    val resultFileName = testDir.getAbsolutePath + "/yosys_results"
    val ret = (s"yosys -s $scriptFileName" #> new File(resultFileName)).!
    val success = (ret == 0)
    (success, btorFileName)
  }



  def apply(c: ir.Circuit, annos: Seq[Annotation]): smt.TransitionSystem = {
    val testDir = createTestDirectory(c.main + "_to_btor2")
    val module = makeVerilog(testDir, c, annos)
    val (success, btorFile) = makeBtor(testDir, module)
    assert(success, "Failed to convert to btor2!")
    smt.Btor2.load(btorFile)
  }


}
