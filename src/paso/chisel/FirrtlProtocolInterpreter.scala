// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import firrtl.annotations.Annotation
import firrtl.ir
import firrtl.ir.Reference
import paso.verification.{ProtocolInterpreter}
import paso.{ExpectAnnotation, MethodIOAnnotation, StepAnnotation}
import uclid.smt

trait RenameMethodIO extends FirrtlInterpreter with HasAnnos {
  val prefix: String = ""
  protected lazy val methodInputs = annos.collect { case MethodIOAnnotation(target, true) => target.ref -> (prefix + target.ref) }.toMap
  protected lazy val methodOutputs = annos.collect { case MethodIOAnnotation(target, false) => target.ref -> (prefix + target.ref) }.toMap
  protected lazy val renameIOs = methodInputs ++ methodOutputs
  override def onReference(r: Reference): smt.Expr = {
    val ref = super.onReference(r)
    renameIOs.get(r.name).map(smt.Symbol(_, ref.typ)).getOrElse(ref)
  }
}

/** protocols built on a custom extension of firrtl */
class FirrtlProtocolInterpreter(name: String, circuit: ir.Circuit, annos: Seq[Annotation], interpreter: ProtocolInterpreter) extends PasoFirrtlInterpreter(circuit, annos) with RenameMethodIO {
  private val steps = annos.collect{ case StepAnnotation(target) => target.ref }.toSet
  private val expects = annos.collect{ case ExpectAnnotation(target) => target.ref }.toSet
  override val prefix = name + "."

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