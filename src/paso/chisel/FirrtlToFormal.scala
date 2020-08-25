// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import uclid.smt
import firrtl.annotations.Annotation
import firrtl.{TargetDirAnnotation, ir}
import firrtl.stage.{FirrtlCircuitAnnotation, FirrtlStage, OutputFileAnnotation}
import firrtl.transforms.NoDCEAnnotation
import firrtl.util.BackendCompilationUtilities
import logger.{LogLevel, LogLevelAnnotation}

object FirrtlToFormal  {
  def apply(c: ir.Circuit, annos: Seq[Annotation]): smt.TransitionSystem = {
    val testDir = BackendCompilationUtilities.createTestDirectory(c.main + "_to_btor2")

    val res = (new FirrtlStage).execute(
      Array("-E", "experimental-btor2"),
      Seq(
        LogLevelAnnotation(LogLevel.Error), // silence warnings for tests
        FirrtlCircuitAnnotation(c),
        TargetDirAnnotation(testDir.getAbsolutePath),
        NoDCEAnnotation,
      ) ++ annos
    )
    val name = res.collectFirst { case OutputFileAnnotation(file) => file }
    assert(name.isDefined)

    val btorFile = testDir.getAbsolutePath + s"/${name.get}.btor2"
    val sys = smt.Btor2.load(btorFile)
    sys.copy(name = Some(c.main))
  }
}
