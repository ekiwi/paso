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
  override def onReference(r: ir.Reference): Value = {
    val ref = super.onReference(r)
    renameIOs.get(r.name).map(name => Value(smt.Symbol(name, ref.typ))).getOrElse(ref)
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

  override def onWhen(cond: Value, tru: ir.Statement, fals: ir.Statement): Unit = {
    def visitTrue() {
      cond_stack.push(cond.get)
      onStmt(tru)
      cond_stack.pop() ;
    }
    def visitFalse() {
      cond_stack.push(app(smt.NegationOp, cond.get))
      onStmt(fals)
      cond_stack.pop()
    }
    interpreter.onWhen(cond.get, visitTrue, visitFalse)
  }

  override def onConnect(name: String, expr: Value): Unit = {
    if(expects.contains(name)) expr.get match {
      case smt.OperatorApplication(smt.EqualityOp, List(lhs, rhs)) =>
        assert(isInput(lhs))
        interpreter.onExpect(lhs, rhs)
      case other => throw new RuntimeException(s"Unexpected pattern for expects: $other")
    } else if(name.startsWith("io_") && isOutput(name)) {
      val s = smt.Symbol(name, outputs(name))
      if(SMTSimplifier.simplify(expr.valid) == fals) {
        interpreter.onUnSet(s)
      } else {
        interpreter.onSet(s, expr.get, sticky = true)
      }
    }
    super.onConnect(name, expr)
  }
}