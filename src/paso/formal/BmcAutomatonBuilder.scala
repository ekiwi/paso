// Copyright 2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.formal

import maltese.passes.ReplaceExpressionsWithSignals
import maltese.{mc, smt}
import paso.protocols._
import paso.untimed.MethodInfo

import java.nio.file.Path

/** Presents an alternative way to [[AutomatonBuilder]] to implement a monitoring automaton for a Paso spec.
 *  This approach is more closely related to the random testing implementation.
 *  - we use an input to select a random protocol (w/ true guard) to execute in a fork state
 *  - we use multiple "PC"s to implement the multi-threading
 *    (for this to work we need to find an upper bound for the number of parallel executions)
 *  - this approach cannot be used to model a sub-component (at least for concrete simulation) because
 *    it does not resolve the non-determinism (we are essentially encoding the NFA directly through the use of
 *    unconstrained inputs)
 * */
class BmcAutomatonBuilder(workingDir: Path) {


  def run(untimed: UntimedModel, protos: Seq[Proto], invert: Boolean): (mc.TransitionSystem, Int) = {
    require(!invert, "Inversion is currently not supported!")
    val maxThreads = determineMaxThreads(protos)

    println(s"MaxThreads: $maxThreads")
    ???
  }


  /**  finds an upper bound for the maximum number of threads that could be active at the same time */
  private def determineMaxThreads(protos: Seq[Proto]): Int = {
    val maxMinCycles = protos.map(_.graph).map(ForkAnalysis.run)
    val minCyclesToFork = maxMinCycles.map(_.minCyclesToFork).min
    val maxCyclesAfterFork = maxMinCycles.map(_.maxCyclesAfterFork).max

    // TODO: check this formula
    scala.math.ceil(maxCyclesAfterFork.toDouble / minCyclesToFork.toDouble).toInt + 1
  }
}
