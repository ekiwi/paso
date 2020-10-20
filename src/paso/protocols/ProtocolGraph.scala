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
case class Transition(name: String, assertions: List[Guarded], assumptions: List[Guarded], mappings: List[Guarded], next: List[Next])

case class Guarded(guards: List[smt.BVExpr], pred: smt.BVExpr) {
  def toExpr: smt.BVExpr = if(guards.isEmpty) { pred } else {
    smt.BVImplies(smt.BVAnd(guards), pred)
  }
}

case class Next(guard: smt.BVExpr, fork: Boolean, cycleId: Int)

object ProtocolGraph {
  def encode(proto: ProtocolPaths): ProtocolGraph = {
    /*
    proto.steps.foreach { case (name, paths) =>
      println(s"Step: $name")
      paths.foreach(println)
    }
    */

    val stepToId = proto.steps.zipWithIndex.map{ case ((name, _), i) => name -> i }.toMap
    val transitions = proto.steps.map{ case (name, paths) => encodeTransition(name, paths, stepToId) }
    // TODO: encode argument state updates
    ProtocolGraph(proto.info, transitions.toArray)
  }

  private def encodeTransition(stepName: String, paths: Seq[PathCtx], stepToId: String => Int): Transition = {
    var mappings = paths.head.prevMappings // prevMappings should be the same for every path!
    // val assumptions = paths.map { p => Guarded(List(p.cond), ) }




    ???
  }
}
