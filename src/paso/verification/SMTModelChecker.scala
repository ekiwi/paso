// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import paso.chisel.SMTHelpers
import uclid.smt
import scala.collection.mutable

/** SMT based bounded model checking as an alternative to dispatching to a btor2 based external solver */
class SMTModelChecker(val solver: Solver, val checkConstraints: Boolean = false) extends SMTHelpers {
  val name: String = "SMTModelChecker with " + solver.name

  def check(sys: smt.TransitionSystem, kMax: Int, defined: Seq[smt.DefineFun] = Seq(), uninterpreted: Seq[smt.Symbol] = Seq()): smt.ModelCheckResult = {
    require(kMax > 0 && kMax <= 2000, s"unreasonable kMax=$kMax")

    // create new context
    solver.push()

    // declare/define functions and encode the transition system
    uninterpreted.foreach(solver.declare)
    defined.foreach(solver.define)
    val enc = new CompactEncoding(sys)
    enc.defineHeader(solver)
    enc.init(solver)

    (0 until kMax).foreach { k =>
      // assume all constraints hold in this step
      sys.constraints.foreach(c => solver.assert(enc.getConstraint(c)))

      // make sure the constraints are not contradictory
      if(checkConstraints) {
        val res = solver.check()
        assert(res.isTrue, s"Found unsatisfiable constraints in cycle $k")
      }

      // check each bad state individually
      sys.bad.foreach { b =>
        solver.push()
        solver.assert(enc.getBadState(b))
        val res = solver.check()
        solver.pop()

        // did we find an assignment for which the bas state is true?
        if(res.isTrue) {
          val w = getWitness(k)
          return smt.ModelCheckFail(w)
        }
      }

      // advance
      enc.unroll(solver)
    }

    // clean up
    solver.pop()
    smt.ModelCheckSuccess()
  }

  private def getWitness(k: Int): smt.Witness = ???

}

/**
 * This Transition System encoding is directly inspired by yosys' SMT backend:
 * https://github.com/YosysHQ/yosys/blob/master/backends/smt2/smt2.cc
 * */
class CompactEncoding(sys: smt.TransitionSystem) extends SMTHelpers {
  private val name = sys.name.get
  private val stateType = smt.UninterpretedType(name + "_s")
  private val stateInitFun = smt.Symbol(name + "_is", smt.MapType(List(stateType), smt.BoolType))
  private val stateTransitionFun = smt.Symbol(name + "_t", smt.MapType(List(stateType, stateType), smt.BoolType))
  private val constraintFuns = sys.constraints.zipWithIndex.map{ case(c,ii) =>
    c -> smt.Symbol(s"c$ii", smt.MapType(List(stateType), smt.BoolType))
  }.toMap
  private val badFuns = sys.bad.zipWithIndex.map{ case(b,ii) =>
    b -> smt.Symbol(s"b$ii", smt.MapType(List(stateType), smt.BoolType))
  }.toMap
  private val states = mutable.ArrayBuffer[smt.Symbol]()


  def defineHeader(solver: Solver): Unit = {
    solver.declare(stateType)

    val stateSymbol = smt.Symbol("state", stateType)
    val nextStateSymbol = smt.Symbol("next_state", stateType)

    // input, output and state functions
    val outputSignals = sys.outputs.map(o => smt.Symbol(o._1, o._2.typ))
    val signals = sys.states.map(_.sym) ++ sys.inputs ++ outputSignals
    val signalFuns = signals.map(s => s -> smt.Symbol(s.id + "_f", smt.MapType(List(stateType), s.typ))).toMap
    val signalSubs = signalFuns.mapValues(f => smt.FunctionApplication(f, List(stateSymbol)))

    // we want to leave state and inputs uninterpreted
    (sys.states.map(_.sym) ++ sys.inputs).foreach(s => solver.declare(signalFuns(s)))

    // outputs can be defined in terms of state and inputs (and maybe other outputs ???)
    sys.outputs.foreach { case (name, expr) =>
      val funExpr = substituteSmtSymbols(expr, signalSubs)
      val funSym = signalFuns(smt.Symbol(name, expr.typ))
      val fun = smt.DefineFun(funSym, List(stateSymbol), funExpr)
      solver.define(fun)
    }

    // define state next and init functions
    val transitionRelations = sys.states.map { s =>
      assert(s.next.nonEmpty, "Next function required")
      val funExpr = substituteSmtSymbols(s.next.get, signalSubs)
      val funSym = smt.Symbol(s.sym.id + "_next", smt.MapType(List(stateType), funExpr.typ))
      val fun = smt.DefineFun(funSym, List(stateSymbol), funExpr)
      solver.define(fun)

      // on a transition, the next state is equal to the result of the next state function applied to the old state
      val newState = smt.FunctionApplication(signalFuns(s.sym), List(nextStateSymbol))
      val nextOldState = smt.FunctionApplication(fun, List(stateSymbol))
      eq(newState, nextOldState)
    }

    val initRelations = sys.states.collect { case s @ smt.State(_, Some(init), _) =>
      val funExpr = substituteSmtSymbols(init, signalSubs)
      val funSym = smt.Symbol(s.sym.id + "_init", smt.MapType(List(stateType), funExpr.typ))
      val fun = smt.DefineFun(funSym, List(stateSymbol), funExpr)
      solver.define(fun)

      // on init, the current state is equal to the init state
      eq(signalSubs(s.sym), smt.FunctionApplication(fun, List(stateSymbol)))
    }

    // define init function
    solver.define(smt.DefineFun(stateInitFun, List(stateSymbol), conjunction(initRelations)))

    // define transition function
    solver.define(smt.DefineFun(stateTransitionFun, List(stateSymbol, nextStateSymbol), conjunction(transitionRelations)))

    // define constraint functions
    constraintFuns.foreach { case (expr, funSym) =>
      val funExpr = substituteSmtSymbols(expr, signalSubs)
      val fun = smt.DefineFun(funSym, List(stateSymbol), funExpr)
      solver.define(fun)
    }

    // define bad state functions
    badFuns.foreach { case (expr, funSym) =>
      val funExpr = substituteSmtSymbols(expr, signalSubs)
      val fun = smt.DefineFun(funSym, List(stateSymbol), funExpr)
      solver.define(fun)
    }
  }

  private def appendState(): smt.Symbol = {
    val s = smt.Symbol(s"s${states.length}", stateType)
    states.append(s)
    s
  }

  def init(solver: Solver): Unit = {
    assert(states.isEmpty)
    val s0 = appendState()
    solver.assert(smt.FunctionApplication(stateInitFun, List(s0)))
  }

  def unroll(solver: Solver): Unit = {
    assert(states.nonEmpty)
    appendState()
    val tStates = states.takeRight(2).toList
    solver.assert(smt.FunctionApplication(stateTransitionFun, tStates))
  }

  /** returns an expression representing the constraint in the current state */
  def getConstraint(e: smt.Expr): smt.Expr = {
    assert(states.nonEmpty)
    val foo = constraintFuns(e)
    smt.FunctionApplication(foo, List(states.last))
  }

  /** returns an expression representing the constraint in the current state */
  def getBadState(e: smt.Expr): smt.Expr = {
    assert(states.nonEmpty)
    val foo = badFuns(e)
    smt.FunctionApplication(foo, List(states.last))
  }

}

object substituteSmtSymbols {
  def apply(expr: smt.Expr, map: Map[smt.Symbol, smt.Expr]): smt.Expr = expr match {
    case e : smt.Symbol => map.get(e).map(apply(_, map)).getOrElse(e)
    case e : smt.OperatorApplication => e.copy(operands = e.operands.map(apply(_, map)))
    case e : smt.Literal => e
    case s : smt.ArraySelectOperation => s.copy(e = apply(s.e, map), index = s.index.map(apply(_, map)))
    case s : smt.ArrayStoreOperation => s.copy(e = apply(s.e, map), index = s.index.map(apply(_, map)), value = apply(s.value, map))
    case f : smt.FunctionApplication => f.copy( e = apply(f.e, map), args = f.args.map(apply(_, map)))
    case other => throw new NotImplementedError(s"TODO: deal with $other")
  }
}