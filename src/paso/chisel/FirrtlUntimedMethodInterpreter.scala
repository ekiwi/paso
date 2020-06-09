// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import firrtl.annotations.Annotation
import firrtl.ir
import paso.untimed.MethodCallAnnotation
import paso.verification.{MethodSemantics, NamedExpr, NamedGuardedExpr, substituteSmt, substituteSmtSymbols}
import uclid.smt

import scala.collection.mutable

class FirrtlUntimedMethodInterpreter(circuit: ir.Circuit, annos: Seq[Annotation]) extends PasoFirrtlInterpreter(circuit, annos) {
  private val methodCalls = annos.collect { case m : MethodCallAnnotation => m }

  // creates function applications for all method calls together with the substitution map
  private def getMethodCallExpressions(): Map[smt.Symbol, smt.Expr] = {
    val originalSubs = methodCalls.groupBy(c => c.name + c.ii).flatMap { case (_, annos) =>
      val methodName = annos.head.name.split('.').last
      val name = annos.head.name + "." + methodName + "_outputs"
      val arg = annos.filter(_.isArg).map(_.target.ref).sorted.map(n => n -> getSimplifiedFinalValue(n).get.e)
      val inTypes = arg.map(_._2.typ).toList
      val ret = annos.filterNot(_.isArg).map(_.target.ref).sorted.map(n => smt.Symbol(n, inputs(n)))
      ret.map { r =>
        val funType = smt.MapType(inTypes, r.typ)
        assert(ret.length == 1, "TODO: chose correct name for multiple return arguments")
        val funSym = smt.Symbol(name, funType)
        val funCall = smt.FunctionApplication(funSym, arg.map(_._2).toList)
        r -> funCall
      }
    }.toMap

    // handle method call that are arguments to other method calls
    var fuel = 1000
    var subs = originalSubs
    while(fuel > 0) {
      val nextFuel = fuel - 1
      fuel = -1
      subs = subs.map { case (sym, app) =>
        val newArgs = app.args.map(substituteSmtSymbols(_, subs))
        val changed = newArgs.zip(app.args).map(p => p._1 != p._2).reduce((a,b) => a || b)
        if(changed) {
          fuel = nextFuel
          sym -> app.copy(args=newArgs)
        } else { sym -> app }
      }
    }
    assert(fuel < 0, "Ran out of fuel. Do you have a recursive method call?")

    subs
  }


  override def onEnterBody(): Unit = {
    // when an untimed module is executing reset should always be false
    refs("reset") = Value(fals)
  }

  def getSemantics(name: String): MethodSemantics = {
    // known prefixes
    val guardName = name + "_guard"
    val inputPrefix = name + "_inputs"
    val outputPrefix = name + "_outputs"
    val enabledName = name + "_enabled"

    // find guard
    val guard = getSimplifiedFinalValue(guardName).map(_.get).getOrElse(tru)

    //
    val memReads = getMemReadExpressions()
    val methCalls = getMethodCallExpressions()
    val enabledSub = Map(smt.Symbol(enabledName, smt.BoolType) -> smt.BooleanLit(true))
    val subs = memReads ++ methCalls ++ enabledSub
    def substituteReadsAndCalls(e: smt.Expr): smt.Expr = substituteSmt(e, subs)

    // collect outputs
    val methodOutputs = this.outputs.keys.filter(_.startsWith(outputPrefix))
    val outputs = methodOutputs.map { o =>
      assert(connections.contains(o), s"Output $o was never assigned!")
      val value = getSimplifiedFinalValue(o).get.map(substituteReadsAndCalls)
      NamedGuardedExpr(smt.Symbol(o, value.typ), value.e, guard=substituteReadsAndCalls(value.valid))
    }

    // collect state updates
    val regUpdates = regs.map { case (name, tpe) =>
      val value = getSimplifiedFinalValue(name).getOrElse(Value(smt.Symbol(name, tpe))).map(substituteReadsAndCalls)
      NamedExpr(smt.Symbol(name, tpe), value.get)
    }
    val memUpdates = mems.values.map { m =>
      NamedExpr(smt.Symbol(m.name, m.typ), substituteReadsAndCalls(getMemUpdates(m.name)))
    }

    // find input types (sorted in order to ensure deterministic argument order for undefined functions)
    val methodInputs = this.inputs.filterKeys(_.startsWith(inputPrefix))
    val ins = methodInputs.map { case (name, tpe) => smt.Symbol(name, tpe) }.toSeq.sortBy(_.id)
    MethodSemantics(guard=guard, updates = (regUpdates ++ memUpdates).toSeq, outputs = outputs.toSeq, inputs = ins)
  }
}