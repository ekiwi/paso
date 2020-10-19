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

case class Next(guard: smt.BVExpr, fork: Boolean, cycleId: Int)

/** the first cycle is always cycles.head */
case class ProtocolGraph(name: String, cycles: Array[Cycle])


/** Encodes imperative protocol into a more declarative graph.
 *  - currently assumes that there are no cycles in the CFG!
 */
class SymbolicProtocolInterpreter(protocol: firrtl.CircuitState, stickyInputs: Boolean = false) extends ProtocolInterpreter(protocol) {
  import ProtocolInterpreter.Loc
  private case class Context()

  // predicates that "guard" the current instructions
  private val guards = mutable.ArrayBuffer[smt.BVExpr]()
  private def guardExpr = guards.foldLeft[smt.BVExpr](smt.True())((a,b) => smt.BVAnd(a, b))

  // keep track of steps we still need to visit
  private val stepsToProcess = mutable.ArrayBuffer[(DoStep, Int)]()
  private var stepCount = 1

  // build a "cycle"
  private var cycle = Cycle("", List(), List(), List(), List())

  def run(): ProtocolGraph = {
    // start executing at block 0
    executeFrom(Loc(0,0))

    // TODO: actual graph!
    ProtocolGraph(name, Array())
  }

  private def executeFrom(loc: Loc): Unit = {
    val stmts = getBlock(loc.block).drop(loc.stmt)
    stmts.map{ case (l, s) => parseStmt(s, l) }.foreach {
      case s: DoStep =>
        onStep(s, loc.stmt + 1 == stmts.length)
        return // end method here
      case s: DoSet => onSet(s)
      case s: DoUnSet => onUnSet(s)
      case s: DoAssert => onAssert(s)
      case s: Goto => onGoto(s)
    }
  }

  private def onSet(set: DoSet): Unit = {
    val value = toSMT(set.expr, inputs(set.loc), allowNarrow = true)

    println(f"SET ${set.loc} <= $value ${set.info.serialize}")
  }
  protected def onUnSet(unset: DoUnSet): Unit = {
    println(f"UNSET ${unset.loc} ${unset.info.serialize}")
  }
  protected def onAssert(a: DoAssert): Unit = {
    val expr = toSMT(a.expr)
    println(f"ASSERT $expr ${a.info.serialize}")
  }
  protected def onGoto(g: Goto): Unit = {
    val cond = toSMT(g.cond)
    println(f"IF $cond GOTO ${g.conseq} ELSE ${g.alt}")
    if(cond == smt.True()) {
      assert(g.alt == -1)
      executeFrom(Loc(g.conseq, 0))
    } else {
      guards.append(cond)
      // TODO: check pc feasibility
      executeFrom(Loc(g.conseq, 0))
      guards.dropRight(1)
      guards.append(simplify(smt.BVNot(cond)))
      // TODO: check pc feasibility
      executeFrom(Loc(g.alt, 0))
      guards.dropRight(1)
    }
  }
  protected def onStep(step: DoStep, isLast: Boolean): Unit = {
    val id = if(isLast) { -1 } else {
      val  i = stepCount ; stepCount += 1
      stepsToProcess.append((step, i))
      i
    }
    val next = Next(guardExpr, step.fork, id)
    cycle = cycle.copy(next = cycle.next :+ next)
    println(f"STEP @ ${step.loc} ${step.info.serialize}")
  }

  def toSMT(expr: ir.Expression, width: Int = 1, allowNarrow: Boolean = false): smt.BVExpr = {
    val e = ExpressionConverter.toMaltese(expr, width, allowNarrow)
    // we simplify once, after converting FIRRTL to SMT
    simplify(e)
  }
  def simplify(e: smt.BVExpr): smt.BVExpr = smt.SMTSimplifier.simplify(e).asInstanceOf[smt.BVExpr]
}