// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import firrtl.annotations.Annotation
import firrtl.ir
import paso.verification.ProtocolInterpreter
import paso.{ExpectAnnotation, MethodIOAnnotation, StepAnnotation}
import uclid.smt
import uclid.smt.Expr

trait RenameMethodIO extends FirrtlInterpreter with HasAnnos {
  val prefix: String = ""
  protected lazy val methodInputs = annos.collect { case MethodIOAnnotation(target, true) => target.ref -> (prefix + target.ref) }.toMap
  protected lazy val methodOutputs = annos.collect { case MethodIOAnnotation(target, false) => target.ref -> (prefix + target.ref) }.toMap
  protected lazy val renameIOs = methodInputs ++ methodOutputs
  override def onReference(r: ir.Reference): smt.Expr = {
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

  override def onWhen(cond: smt.Expr, tru: ir.Statement, fals: ir.Statement): Unit = {
    def visitTrue() {
      cond_stack.push(cond)
      onStmt(tru)
      cond_stack.pop() ;
    }
    def visitFalse() {
      cond_stack.push(app(smt.NegationOp, cond))
      onStmt(fals)
      cond_stack.pop()
    }
    interpreter.onWhen(cond, visitTrue, visitFalse)
  }

  override def onConnect(name: String, expr: smt.Expr): Unit = {
    if(expects.contains(name)) expr match {
      case smt.OperatorApplication(smt.EqualityOp, List(lhs, rhs)) =>
        assert(isInput(lhs))
        interpreter.onExpect(lhs, rhs)
      case other => throw new RuntimeException(s"Unexpected pattern for expects: $other")
    } else if(name.startsWith("io_") && isOutput(name)) {
      interpreter.onSet(smt.Symbol(name, outputs(name)), expr, sticky=true)
    }
    super.onConnect(name, expr)
  }

  override def onIsInvalid(expr: Expr): Unit = expr match {
    case s @ smt.Symbol(name, typ) =>
      assert(name.startsWith("io_") && isOutput(name), f"Unexpected signal $name : $typ")
      interpreter.onUnSet(s)
  }
}