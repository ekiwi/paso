// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.ir
import maltese.smt

/** represents a "cycle" (the period between two state transitions) of the protocol:
 * - all assertions over the outputs in this cycle are encoded as boolean formulas with the input constraints as guards
 *   like: `in := 1 ; assert(out == 2)` gets encoded as `(in = 1) => (out = 2)`
 * - the final input assumptions, i.e. the stable input signals that will determine the next state are also
 *   encoded separately
 * - final input assumptions depend on the same path guards as the next cycle
 * - there could be different next cycles depending on ret/arg or module i/o, these are encoded as a priority list
 *   with guards that need to be evaluated from front to back, the first guard which is true is the transition that
 *   should be taken
 * - TODO: encode mapping of method args (the first time args are applied to the inputs, they are treated as a mapping,
 *         after that they are a constraint)
 * */
case class Cycle(name: String, assertions: List[Guarded], next: List[Next])

case class Guarded(guards: List[smt.BVExpr], pred: smt.BVExpr) {
  def toExpr: smt.BVExpr = if(guards.isEmpty) { pred } else {
    smt.BVImplies(smt.BVAnd(guards), pred)
  }
}

case class Next(guards: List[smt.BVExpr], inputAssumptions: List[smt.BVExpr], mappings: List[smt.BVExpr], cycleId: Int)

/** the first cycle is always cycles.head */
case class ProtocolGraph(name: String, cycles: Array[Cycle])


/** Encodes imperative protocol into a more declarative graph  */
class SymbolicProtocolInterpreter(protocol: firrtl.CircuitState, methodPrefix: String, ioPrefix: String) {
  def run(): ProtocolGraph = ???
}
