// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel.passes

import firrtl.annotations._

case class ChangeAnnotationCircuit(newCircuit: String) {
  private def change(n: Named): Named = n match {
    case t: ModuleTarget => t.copy(circuit = newCircuit)
    case t: ReferenceTarget => t.copy(circuit = newCircuit)
    case other => throw new NotImplementedError(s"TODO: support $other : ${other.getClass.getName}")
  }

  def apply(anno: Annotation): Annotation = anno match {
    case t: SingleTargetAnnotation[_] => t.asInstanceOf[SingleTargetAnnotation[Named]].duplicate(change(t.target))
    case other => throw new NotImplementedError(s"TODO: support $other : ${other.getClass.getName}")
  }
}
