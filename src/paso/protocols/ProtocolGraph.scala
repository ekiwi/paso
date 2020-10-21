// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import maltese.smt

/** the first cycle is always cycles.head */
case class ProtocolGraph(info: ProtocolInfo, transitions: Array[Transition])

/** represents a transition of the protocol:
 * - all assertions over the outputs in this transition are encoded as boolean formulas with the input constraints as guards
 *   like: `in := 1 ; assert(out == 2)` gets encoded as `(in = 1) => (out = 2)` TODO: not true
 * - the final input assumptions, i.e. the stable input signals that will determine the next state are also
 *   encoded separately as guarded assumptions. The guard in this case is the path condition.
 *   ```
 *   in := 1
 *   when c:
 *     in := 2
 *   ```
 *   results in: `(c => (in = 2)) and (not(c) => (in = 1))`
 *   it might be better to encode this as `in = ite(c, 2, 1)` ...
 * - final input assumptions depend on the same path guards as the next cycle
 * - there could be different next cycles depending on ret/arg or module i/o, these are encoded as a priority list
 *   with guards that need to be evaluated from front to back, the first guard which is true is the transition that
 *   should be taken
 * - TODO: encode mapping of method args (the first time args are applied to the inputs, they are treated as a mapping,
 *         after that they are a constraint)
 * */
case class Transition(
  name: String, assertions: Seq[Guarded], assumptions: Seq[Guarded],
  mappings: Seq[GuardedMapping], ioAccess: Seq[GuardedAccess], next: Seq[Next]
)

case class GuardedAccess(guard: smt.BVExpr, pin: String, bits: BigInt)

case class Guarded(guard: smt.BVExpr, pred: smt.BVExpr) {
  def toExpr: smt.BVExpr = if(guard == smt.True()) { pred } else { smt.BVImplies(guard, pred) }
}

case class GuardedMapping(guard: smt.BVExpr, arg: String, bits: BigInt, update: smt.BVExpr)

/**
 * @param guard   if true, we go to cycleId
 * @param fork    indicates whether new transactions can be started in the next cycle
 * @param commit  list of commit signals that need to be asserted in order to advance the state of the transactional model
 * @param cycleId index of the next cycle
 */
case class Next(guard: smt.BVExpr, fork: Boolean, commit: Seq[smt.BVSymbol], cycleId: Int)

object ProtocolGraph {
  def encode(proto: ProtocolPaths): ProtocolGraph = {
    val stepToId = proto.steps.zipWithIndex.map{ case ((name, _), i) => name -> i }.toMap
    val transitions = proto.steps.map{ case (name, paths) => encodeTransition(name, paths, stepToId, proto.info) }
    // TODO: encode argument state updates
    ProtocolGraph(proto.info, transitions.toArray)
  }

  private def encodeTransition(stepName: String, paths: Seq[PathCtx], stepToId: String => Int, info: ProtocolInfo): Transition = {
    // find the assumptions and mappings for all paths
    val am = paths.map { p =>
      var mappings = paths.head.prevMappings
      val am = p.inputValues.map { case (input, v) =>
        val r = BitMapping.analyze(mappings, smt.BVSymbol(input, v.value.width), v.value)
        mappings = r._3
        (r._1, r._2)
      }
      (am.flatMap(_._1).map(simplify).map(Guarded(p.cond, _)), am.flatMap(_._2).map(simplify).map(Guarded(p.cond, _)))
    }
    val (assumptions, mappings) = (am.flatMap(_._1), am.flatMap(_._2))

    // find the assertions for all paths
    val assertions = paths.flatMap{ p => p.asserts.map(simplify).map(Guarded(p.cond, _)) }

    // find the next states
    val next = paths.flatMap{ p => p.next.map{ nextName =>
      val nextInfo = info.steps(nextName)
      // we commit if it is the final node and the execution has not forked yet, or if it is a fork node
      val doCommit = (nextInfo.isFinal && !p.hasForked) || nextInfo.doFork
      val commit = if(doCommit) List(smt.BVSymbol(info.methodPrefix + "enabled", 1)) else List()
      Next(p.cond, nextInfo.doFork, commit, stepToId(nextName))
    }}

    // find all I/O pins that are accessed
    val ioAccess = findIOUses(info.ioPrefix, assumptions ++ mappings ++ assertions) ++ findIOGuardUses(info.ioPrefix, paths)

    Transition(stepName, assertions, assumptions, mappings.map(exprToMapping), ioAccess.toList, next)
  }

  private def exprToMapping(e: Guarded): GuardedMapping = {
    val eq = e.pred.asInstanceOf[smt.BVEqual]
    val input = eq.a
    val (arg, hi, lo) = eq.b match {
      case s : smt.BVSymbol => (s, s.width-1, 0)
      case smt.BVSlice(s: smt.BVSymbol, hi, lo) => (s, hi, lo)
      case other => throw new RuntimeException(s"Unexpected argument mapping expr: $other")
    }

    // if not the whole arg is update at once, we need to retain some of the previous state
    val prev = arg.rename(arg.name + ".prev")
    val leftPad = if(hi == arg.width - 1) { input }
    else { smt.BVConcat(smt.BVSlice(prev, arg.width-1, hi + 1), input) }
    val rightPad = if(lo == 0) { leftPad }
    else { smt.BVConcat(leftPad, smt.BVSlice(prev, lo-1, 0)) }

    GuardedMapping(e.guard, arg.name, BitMapping.toMask(hi, lo), rightPad)
  }

  private def findIOGuardUses(ioPrefix: String, p: Iterable[PathCtx]): Iterable[GuardedAccess] =
    findIOUses(ioPrefix, Guarded(smt.True(), smt.BVOr(p.map(_.cond))))
  private def findIOUses(ioPrefix: String, g: Iterable[Guarded]): Iterable[GuardedAccess] =
    g.flatMap(findIOUses(ioPrefix, _))
  private def findIOUses(ioPrefix: String, g: Guarded): Iterable[GuardedAccess] =
    BitMapping.mappedBits(g.pred).filter(_._1.startsWith(ioPrefix)).map { case (name, bits) => GuardedAccess(g.guard, name, bits) }

  private def simplify(e: smt.BVExpr): smt.BVExpr = smt.SMTSimplifier.simplify(e).asInstanceOf[smt.BVExpr]
}
