// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import firrtl.{LowFirrtlEmitter, ir}
import firrtl.stage.{FirrtlCircuitAnnotation, FirrtlStage, RunFirrtlTransformAnnotation}
import treadle.stage.TreadleTesterPhase
import treadle.{TreadleTester, TreadleTesterAnnotation, WriteVcdAnnotation}

/** Small helper to turn loFirrtl into a TreadleTester*/
object MakeTreadleTester {
  def apply(state: firrtl.CircuitState, vcd: Boolean): TreadleTester = {
    val loFirrtl = Seq(FirrtlCircuitAnnotation(state.circuit))
    val vcdAnno = if(vcd) Some(WriteVcdAnnotation) else None

    val annos = loFirrtl ++ vcdAnno
    val tester = (new TreadleTesterPhase).transform(annos)
      .collectFirst { case TreadleTesterAnnotation(t) => t }.getOrElse(
      throw new RuntimeException("Failed to create a treadle tester for the implementation!")
    )

    tester
  }

}
