// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import firrtl.annotations.DeletedAnnotation
import firrtl.backends.experimental.smt.ExpressionConverter
import firrtl.{AnnotationSeq, ir}
import firrtl.stage.{FirrtlCircuitAnnotation, FirrtlStage, OutputFileAnnotation}
import firrtl.transforms.NoCircuitDedupAnnotation
import logger.{LogLevel, LogLevelAnnotation}
import maltese.mc.TransitionSystem

object FirrtlToFormal  {
  def apply(c: ir.Circuit, annos: AnnotationSeq, ll: LogLevel.Value = LogLevel.Error): (TransitionSystem, AnnotationSeq) = {
    // TODO: ensure that firrtl.transforms.formal.AssertSubmoduleAssumptions is not run!

    val combinedAnnos = Seq(
      LogLevelAnnotation(ll),
      FirrtlCircuitAnnotation(c),
      NoCircuitDedupAnnotation, // since we flatten everything anyways, there is no need to dedup.
    ) ++ annos
    val res = (new FirrtlStage).execute(Array("-E", "experimental-btor2"), combinedAnnos)
    val name = res.collectFirst { case OutputFileAnnotation(file) => file }
    assert(name.isDefined)

    val resAnnos = res.filterNot(_.isInstanceOf[DeletedAnnotation])

    val sys = ExpressionConverter.toMaltese(resAnnos).getOrElse(throw new RuntimeException("Failed to find transition system annotation!"))
    (sys, resAnnos)
  }
}
