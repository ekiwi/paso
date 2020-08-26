// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import uclid.smt
import firrtl.annotations.{Annotation, CircuitName, ModuleName}
import firrtl.options.{Dependency,TargetDirAnnotation}
import firrtl.ir
import firrtl.stage.{FirrtlCircuitAnnotation, FirrtlStage, OutputFileAnnotation, RunFirrtlTransformAnnotation}
import firrtl.transforms.{Flatten, FlattenAnnotation, NoDCEAnnotation}
import firrtl.util.BackendCompilationUtilities
import logger.{LogLevel, LogLevelAnnotation}

object FirrtlToFormal  {
  def apply(c: ir.Circuit, annos: Seq[Annotation]): smt.TransitionSystem = {
    val testDir = BackendCompilationUtilities.createTestDirectory(c.main + "_to_btor2")


    val main = ModuleName(c.main, CircuitName(c.main))
    // TODO: remove once https://github.com/freechipsproject/firrtl/pull/1868 is fixed
    // try to work around a bug in the Flatten/Inline pass that makes firrtl crash when there is nothing to inline
    val flatten = if(c.modules.size > 1) {
      Seq(FlattenAnnotation(main), RunFirrtlTransformAnnotation(Dependency[Flatten]))
    } else Seq()

    val res = (new FirrtlStage).execute(
      Array("-E", "experimental-btor2"),
      Seq(
        LogLevelAnnotation(LogLevel.Error), // silence warnings for tests
        FirrtlCircuitAnnotation(c),
        TargetDirAnnotation(testDir.getAbsolutePath),
        NoDCEAnnotation,
      ) ++ flatten ++ annos
    )
    val name = res.collectFirst { case OutputFileAnnotation(file) => file }
    assert(name.isDefined)

    val btorFile = testDir.getAbsolutePath + s"/${name.get}.btor2"
    val sys = smt.Btor2.load(btorFile)
    sys.copy(name = Some(c.main))
  }
}
