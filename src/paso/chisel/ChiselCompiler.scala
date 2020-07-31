// Copyright 2020, SiFive, Inc
// released under Apache License Version 2.0
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import chisel3.RawModule
import chisel3.stage._
import chisel3.stage.phases.Convert
import firrtl.stage.{FirrtlCircuitAnnotation, Forms, TransformManager}

/** Allows programmatic access to the Builder elaboration and the Converter to Firrtl */
object ChiselCompiler {
  private val converter = new Convert
  def elaborate[M <: RawModule](gen: () => M): (firrtl.CircuitState, M) = {
    // run Builder.build(Module(gen()))
    val genAnno = ChiselGeneratorAnnotation(gen)
    val elaborationAnnos = genAnno.elaborate

    // extract elaborated module
    val dut = elaborationAnnos.collectFirst{ case DesignAnnotation(d) => d}.get

    // run Converter.convert(a.circuit) and toFirrtl on all annotations
    val converterAnnos = converter.transform(elaborationAnnos)
    val chirrtl = converterAnnos.collectFirst { case FirrtlCircuitAnnotation(c) => c }.get
    val annos = converterAnnos.filterNot(_.isInstanceOf[FirrtlCircuitAnnotation])
    val state = firrtl.CircuitState(chirrtl, annos)

    (state, dut.asInstanceOf[M])
  }
}

object FirrtlCompiler {
  private def lowFirrtlCompiler = new TransformManager(Forms.LowForm)
  def toLowFirrtl(state: firrtl.CircuitState): firrtl.CircuitState = lowFirrtlCompiler.runTransform(state)
  private def highFirrtlCompiler = new TransformManager(Forms.HighForm)
  def toHighFirrtl(state: firrtl.CircuitState): firrtl.CircuitState = highFirrtlCompiler.runTransform(state)
}