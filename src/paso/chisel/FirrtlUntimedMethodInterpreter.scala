// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import firrtl.annotations.Annotation
import firrtl.ir
import paso.verification.{MethodSemantics, NamedExpr, NamedGuardedExpr, substituteSmt}
import paso.{GuardAnnotation, MethodIOAnnotation}
import uclid.smt

import scala.collection.mutable

class FirrtlUntimedMethodInterpreter(circuit: ir.Circuit, annos: Seq[Annotation]) extends PasoFirrtlInterpreter(circuit, annos) with RenameMethodIO {
  private val guards = annos.collect { case GuardAnnotation(target) => target.ref }.toSet
  assert(guards.size == 1, "Exactly one guard expected")

  override def onEnterBody(): Unit = {
    // when an untimed module is executing reset should always be false
    refs("reset") = Value(fals)
  }

  def getSemantics: MethodSemantics = {
    // find guard
    val guard = getSimplifiedFinalValue(guards.head).map(_.get).getOrElse(tru)

    //
    val memReads = getMemReadExpressions()
    def substituteReads(e: smt.Expr): smt.Expr = substituteSmt(e, memReads)

    // collect outputs
    val outputs = methodOutputs.values.map { o =>
      assert(connections.contains(o), s"Output $o was never assigned!")
      val value = getSimplifiedFinalValue(o).get.map(substituteReads)
      NamedGuardedExpr(smt.Symbol(o, value.typ), value.e, guard=substituteReads(value.valid))
    }

    // collect state updates
    val regUpdates = regs.map { case (name, tpe) =>
      val value = getSimplifiedFinalValue(name).getOrElse(Value(smt.Symbol(name, tpe))).map(substituteReads)
      NamedExpr(smt.Symbol(name, tpe), value.get)
    }
    val memUpdates = mems.values.map { m =>
      NamedExpr(smt.Symbol(m.name, m.typ), substituteReads(getMemUpdates(m.name)))
    }

    // find input types
    val ins = methodInputs.map { case (from, to) => smt.Symbol(to, inputs(from)) }
    MethodSemantics(guard=guard, updates = (regUpdates ++ memUpdates).toSeq, outputs = outputs.toSeq, inputs = ins.toSeq)
  }
}