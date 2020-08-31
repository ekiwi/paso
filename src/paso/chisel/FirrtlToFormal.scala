// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import uclid.smt
import firrtl.annotations.DeletedAnnotation
import firrtl.options.{Dependency, TargetDirAnnotation}
import firrtl.{AnnotationSeq, ir}
import firrtl.stage.{FirrtlCircuitAnnotation, FirrtlStage, OutputFileAnnotation, RunFirrtlTransformAnnotation}
import firrtl.util.BackendCompilationUtilities
import logger.{LogLevel, LogLevelAnnotation}

object FirrtlToFormal  {
  def apply(c: ir.Circuit, annos: AnnotationSeq): (smt.TransitionSystem, AnnotationSeq) = {
    val testDir = BackendCompilationUtilities.createTestDirectory(c.main + "_to_btor2")
    val res = (new FirrtlStage).execute(
      Array("-E", "experimental-btor2"),
      Seq(
        LogLevelAnnotation(LogLevel.Error), // silence warnings for tests
        FirrtlCircuitAnnotation(c),
        TargetDirAnnotation(testDir.getAbsolutePath),
        RunFirrtlTransformAnnotation(Dependency[firrtl.passes.InlineInstances]),
      ) ++ annos
    )
    val name = res.collectFirst { case OutputFileAnnotation(file) => file }
    assert(name.isDefined)

    val resAnnos = res.filterNot(_.isInstanceOf[DeletedAnnotation])

    val btorFile = testDir.getAbsolutePath + s"/${name.get}.btor2"
    println(btorFile)
    val sys = smt.Btor2.load(btorFile)
    (sys.copy(name = Some(c.main)), resAnnos)
  }
}
