// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import uclid.smt
import paso.untimed

case class UntimedModel(sys: smt.TransitionSystem, methods: Seq[untimed.MethodInfo])
/*

object UntimedModel {
  def functionAppSubs(m: UntimedModel): Iterable[(smt.Symbol, smt.FunctionApplication)] = m.methods.flatMap { case( name, meth) =>
    meth.outputs.flatMap(o => Seq(o.sym -> o.functionApp, o.guardSym -> o.guardFunctionApp)) ++
    // for state updated we need to add the s".$name" suffix to avoid name conflicts
      meth.updates.map(u => u.copy(sym = u.sym.copy(id = u.sym.id + s".$name"))).map(u => u.sym -> u.functionApp)
  }
  def functionDefs(m: UntimedModel): Iterable[smt.DefineFun] = m.methods.flatMap { case( name, meth) =>
    meth.outputs.flatMap(o => Seq(o.functionDef, o.guardFunctionDef)) ++
      // for state updated we need to add the s".$name" suffix to avoid name conflicts
      meth.updates.map(u => u.copy(sym = u.sym.copy(id = u.sym.id + s".$name"))).map(_.functionDef)
  }
  def functionDefAlias(m: UntimedModel, a: UntimedModel): Iterable[smt.DefineFun] = {
    assert(m.state.isEmpty && a.state.isEmpty, "TODO: support submodules with state")
    def alias(x: smt.DefineFun, y: smt.DefineFun): smt.DefineFun = {
      x.copy(e = smt.FunctionApplication(y.id, x.args))
    }
    m.methods.flatMap { case (name, meth) => meth.outputs.flatMap { o =>
      val aliasMeth = a.methods(name)
      val outputName = o.sym.id.split('.').last
      val ao = aliasMeth.outputs.find(_.sym.id.endsWith(outputName)).get
      Seq(alias(o.functionDef, ao.functionDef), alias(o.guardFunctionDef, ao.guardFunctionDef))
    }}
  }
}

trait IsFunction {
  val sym: smt.Symbol
  val expr: smt.Expr
  private lazy val args = smt.Context.findSymbols(expr).toList.sortBy(_.id)
  private lazy val funSym = smt.Symbol(sym.id, smt.MapType(args.map(_.typ), expr.typ))
  def functionApp: smt.FunctionApplication = smt.FunctionApplication(funSym, args)
  def functionDef: smt.DefineFun = smt.DefineFun(funSym, args, expr)
}

case class NamedExpr(sym: smt.Symbol, expr: smt.Expr) extends IsFunction
case class NamedGuardedExpr(sym: smt.Symbol, expr: smt.Expr, guard: smt.Expr) extends IsFunction {
  val guardSym = smt.Symbol(sym.id + ".valid", smt.BoolType)
  private lazy val guardArgs = smt.Context.findSymbols(guard).toList.sortBy(_.id)
  private lazy val guardFunSym = smt.Symbol(guardSym.id, smt.MapType(guardArgs.map(_.typ), smt.BoolType))
  def guardFunctionApp: smt.FunctionApplication = smt.FunctionApplication(guardFunSym, guardArgs)
  def guardFunctionDef: smt.DefineFun = smt.DefineFun(guardFunSym, guardArgs, guard)
}
*/