// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.backends.experimental.smt.ExpressionConverter
import firrtl.ir
import maltese.smt

import scala.collection.mutable

/** represents a "cycle" (the period between two state transitions) of the protocol:
 * - all assertions over the outputs in this cycle are encoded as boolean formulas with the input constraints as guards
 *   like: `in := 1 ; assert(out == 2)` gets encoded as `(in = 1) => (out = 2)`
 * - the final input assumptions, i.e. the stable input signals that will determine the next state are also
 *   encoded separately as guarded assumptions. The guard in this case is the path condition.
 *   ```
 *   in := 1
 *   when c:
 *     in := 2
 *   ``
 *   results in: `(c => (in = 2)) and (not(c) => (in = 1))`
 *   it might be better to encode this as `in = ite(c, 2, 1)` ...
 * - final input assumptions depend on the same path guards as the next cycle
 * - there could be different next cycles depending on ret/arg or module i/o, these are encoded as a priority list
 *   with guards that need to be evaluated from front to back, the first guard which is true is the transition that
 *   should be taken
 * - TODO: encode mapping of method args (the first time args are applied to the inputs, they are treated as a mapping,
 *         after that they are a constraint)
 * */
case class Cycle(name: String, assertions: List[Guarded], assumptions: List[Guarded], mappings: List[Guarded], next: List[Next])

case class Guarded(guards: List[smt.BVExpr], pred: smt.BVExpr) {
  def toExpr: smt.BVExpr = if(guards.isEmpty) { pred } else {
    smt.BVImplies(smt.BVAnd(guards), pred)
  }
}

case class Next(guard: smt.BVExpr, doCommit: Boolean, cycleId: Int)

/** the first cycle is always cycles.head */
case class ProtocolGraph(name: String, cycles: Array[Cycle])


/** Encodes imperative protocol into a more declarative graph.
 *  - currently assumes that there are no cycles in the CFG!
 */
class SymbolicProtocolInterpreter(protocol: firrtl.CircuitState, stickyInputs: Boolean = false) extends ProtocolInterpreter(protocol) {
  private case class Context()

  private val pathCondition = mutable.ArrayBuffer[smt.BVExpr]()

  def run(): ProtocolGraph = {
    // start executing at block 0
    onBlock(0)

    // TODO: actual graph!
    ProtocolGraph(name, Array())
  }

  private def executeFrom(loc: Loc): Unit = {
    val stmts = getBlock(loc.block).drop(loc.stmt)
    stmts.foreach {
      case (_, stmt: ) =>

    }

  }

  override protected def onSet(info: ir.Info, loc: String, expr: ir.Expression): Unit = {
    val value = toSMT(expr, inputs(loc), allowNarrow = true)
    /*
    value match {
      case l : smt.BVLiteral =>
    }

     */


    println(f"SET $loc <= $value ${info.serialize}")
  }
  override protected def onUnSet(info: ir.Info, loc: String): Unit = {
    println(f"UNSET $loc ${info.serialize}")
  }
  override protected def onAssert(info: ir.Info, expr: ir.Expression): Unit = {
    val smt = toSMT(expr)
    println(f"ASSERT $smt ${info.serialize}")
  }
  override protected def onGoto(g: Goto): Unit = {
    val cond = toSMT(g.cond)
    println(f"IF $cond GOTO ${g.conseq} ELSE ${g.alt}")
    if(cond == smt.True()) {
      assert(g.alt == -1)
      onBlock(g.conseq)
    } else {
      pathCondition.append(cond)
      // TODO: check pc feasibility
      onBlock(g.conseq)
      pathCondition.dropRight(1)
      pathCondition.append(simplify(smt.BVNot(cond)))
      // TODO: check pc feasibility
      onBlock(g.alt)
      pathCondition.dropRight(1)
    }
  }
  override protected def onStep(info: ir.Info, loc: Loc, name: String): Unit = {
    println(f"STEP @ $loc ${info.serialize}")
  }
  override protected def onFork(info: ir.Info, loc: Loc, name: String): Unit = {
    println(f"FORK @ $loc ${info.serialize}")
  }
  private def toSMT(expr: ir.Expression, width: Int = 1, allowNarrow: Boolean = false): smt.BVExpr = {
    val e = ExpressionConverter.toMaltese(expr, width, allowNarrow)
    // we simplify once, after converting FIRRTL to SMT
    simplify(e)
  }
  private def simplify(e: smt.BVExpr): smt.BVExpr = smt.SMTSimplifier.simplify(e).asInstanceOf[smt.BVExpr]
}
