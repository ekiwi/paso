// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import firrtl.annotations.Annotation
import firrtl.ir
import paso.verification.ProtocolInterpreter
import paso.{ExpectAnnotation, StepAnnotation}
import uclid.smt

object FirrtlProtocolInterpreter {
  def run(circuit: ir.Circuit, annos: Seq[Annotation]): Unit ={
    val int = new ProtocolInterpreter
    new FirrtlProtocolInterpreter(circuit, annos, int).run()
    val graph = int.getGraph
    println(graph)
  }
}

/** protocols built on a custom extension of firrtl */
class FirrtlProtocolInterpreter(circuit: ir.Circuit, annos: Seq[Annotation], interpreter: ProtocolInterpreter) extends PasoFirrtlInterpreter(circuit, annos) {
  override def defWire(name: String, tpe: ir.Type): Unit = {
    if(steps.contains(name)) { interpreter.onStep() }
    super.defWire(name, tpe)
  }

  override def onConnect(name: String, expr: smt.Expr): Unit = {
    if(expects.contains(name)) expr match {
      case smt.OperatorApplication(smt.EqualityOp, List(lhs, rhs)) =>
        assert(isInput(lhs))
        interpreter.onExpect(lhs, rhs)
      case other => throw new RuntimeException(s"Unexpected pattern for expects: $other")
    } else if(name.startsWith("io_") && isOutput(name)) {
      interpreter.onSet(smt.Symbol(name, outputs(name)), expr)
    }
    super.onConnect(name, expr)
  }
}