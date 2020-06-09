// Copyright 2020, SiFive, Inc
// released under Apache License Version 2.0
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.untimed
import chisel3.stage._
import chisel3._
import firrtl.annotations.DeletedAnnotation
import firrtl.stage.FirrtlCircuitAnnotation
import firrtl.{EmittedFirrtlCircuitAnnotation, ir}
import paso.UntimedModule

object ElaborateUntimed {
  private val stage = new chisel3.stage.ChiselStage
  private def toLowFirrtl[M <: RawModule](gen: () => M): ir.Circuit = {
    val annos = Seq()
    val r = stage.execute(Array("-X", "low"), ChiselGeneratorAnnotation(gen) +: annos)
    // retrieve circuit
    r.collectFirst { case FirrtlCircuitAnnotation(a) => a }.get
  }

  def apply[M <: UntimedModule](m: => M): M = {
    var mod: Option[M] = None
    val gen = () => {
      mod = Some(m)
      // generate the circuit for each method
      mod.get.methods.foreach(_.generate())
      mod.get
    }
    val fir = toLowFirrtl(gen)
    mod.get._isElaborated = true


    mod.get
  }
}
