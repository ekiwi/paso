// Copyright 2020-2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.formal

import maltese.passes.ReplaceExpressionsWithSignals
import maltese.{mc, smt}
import paso.protocols._
import paso.untimed.MethodInfo

import java.nio.file.Path

class AutomatonBuilder(solver: smt.Solver, workingDir: Path) {

  def run(untimed: UntimedModel, protos: Seq[Proto], invert: Boolean, doFork: Boolean): (mc.TransitionSystem, Int) = {
    val longest = longestPath(protos.map(_.graph))

    val prefix = untimed.sys.name + ".automaton."
    val (cfgAuto, graphInfo) = buildControlAutomaton(prefix, protos, invert, doFork)

    //println("==============")
    //println("New Automaton:")
    //println("==============")
    //println(auto.serialize)
    //println()

    val utAuto = connectUntimed(untimed, graphInfo)

    // combine control flow automaton and modified untimed spec
    val combined = mc.TransitionSystem.combine(utAuto.name, List(cfgAuto, utAuto))
    (TopologicalSort.run(combined), longest)
  }

  private def longestPath(protocols: Iterable[UGraph]): Int = protocols.map(FindLongestPath.run).max

  private def buildControlAutomaton(prefix: String, protos: Seq[Proto], invert: Boolean, doFork: Boolean):
  (mc.TransitionSystem, Seq[ProtoGraphInfo]) = {
    val info = protos.map(_.info)

    // first we check to see when the protocols commit
    val commits = protos.map { case Proto(i, p) =>
      new CommitAnalysis(i.rets).run(p)
    }
    val commitInfo = commits.map(_._2)

    val tagPasses = Seq(new TagInternalNodes("Active"), new TagStartNode("Start"),
      new RemoveEmptyLeafStates(Set("HasCommitted")))
    val taggedProtocols = commits.map(_._1).map { p => tagPasses.foldLeft(p)((old, pass) => pass.run(old)) }

    val prefixArgsPass = new PrefixArgs(info)
    val prefixedProtocols = taggedProtocols.zip(info).map { case(p, i) =>
      prefixArgsPass.run(new PrefixSignals(i.name + "$0_", Set("fork")).run(p))
    }

    // trying to make a paso automaton out of u graphs
    val b = new UGraphBuilder("combined")
    val start = b.addNode("start", List(UAction(ASignal(prefix + "StartState"))))
    prefixedProtocols.zip(info).foreach { case (p, i) =>
      val protoStart = b.addGraph(p)
      val guard = smt.BVSymbol(i.methodPrefix + "guard", 1)
      b.addEdge(start, protoStart, guard)
    }
    val combined = b.get
    ProtocolVisualization.saveDot(combined, false, s"$workingDir/combined.dot")

    val combinedWithAssumptionGuards = AssumptionsToGuards.run(combined)
    ProtocolVisualization.saveDot(combinedWithAssumptionGuards, false, s"$workingDir/combined.guards.dot")

    val gSolver = new GuardSolver(solver)
    val makeDet = new MakeDeterministic(gSolver)
    val passes = Seq(RemoveAsynchronousEdges, makeDet, new MergeActionsAndEdges(gSolver))
    val merged = passes.foldLeft(combinedWithAssumptionGuards)((in, pass) => pass.run(in))
    ProtocolVisualization.saveDot(merged, false, s"$workingDir/merged.dot")

    val (forked, protocolInstances) = if(doFork) {
      resolveForks(gSolver, info, merged)
    } else {
      // only one instance per protocol
      val instances = protos.map(_ => List(0))
      (merged, instances)
    }

    // turn guards back into assumptions and remove signals that are no longer needed:
    val guardsToAssumptions = new GuardsToAssumptions(gSolver)
    val removeSignals = new RemoveSignalsEndingWith(List("Active", "AllMapped"))
    val removeSignals2 = new RemoveSignalsStartingWith(List("Starting: ")) // remove signals added by forking pass
    val simplified = removeSignals2.run(removeSignals.run(guardsToAssumptions.run(forked)))

    // make automaton
    ProtocolVisualization.saveDot(simplified, false, s"$workingDir/final_control.dot")
    val enableAssertions = smt.BVNot(smt.BVOr(reset, finalStep))
    val auto = new UGraphToTransitionSystem(gSolver).run(simplified, invert=invert, prefix=prefix, enableAssertions=enableAssertions)

    //println("Protocols:  " + info.map(_.name).mkString(", "))
    //println("CommitInfo: " + commitInfo.toString)
    //println("Instances:  " + protocolInstances)
    assert(commitInfo.size == protocolInstances.size)
    val graphInfo = commitInfo.zip(protocolInstances).zip(protos).map { case ((c, i), p) =>
      ProtoGraphInfo(p.name, c.readAfterCommit, c.mapInputsBeforeCommit, i)
    }.toSeq

    // many signals end up being the same expression:
    (ReplaceExpressionsWithSignals.run(auto), graphInfo)
  }

  private def resolveForks(gSolver: GuardSolver, info: Seq[ProtocolInfo], merged: UGraph): (UGraph, Seq[Seq[Int]]) = {
    val forkPass = new ExpandForksPass(info, gSolver, workingDir.toString)
    val forksExpanded = forkPass.run(merged)
    val protocolInstances = forkPass.getProtocolInstances
    ProtocolVisualization.saveDot(forksExpanded, false, s"$workingDir/fork.dot")
    (forksExpanded, protocolInstances)
  }

  private case class ProtoGraphInfo(name: String, readAfterCommit: Boolean, mapInputsBeforeCommit: Boolean, instances: Seq[Int])

  private val reset = smt.BVSymbol("reset", 1)
  // in the final step of an induction, we do not need to assert anything besides that the invariants hold
  private val finalStep = smt.BVSymbol("finalStep", 1)

  private def connectUntimed(untimed: UntimedModel, graphInfo: Seq[ProtoGraphInfo]): mc.TransitionSystem = {
    // the verification task might not make use of all of the untimed model's methods
    val isUsed = graphInfo.map(_.name).toSet
    val (usedMethods, ignoredMethods) = untimed.methods.partition(m => isUsed(m.fullName))
    require(graphInfo.length == usedMethods.length, s"$graphInfo, $usedMethods")

    // for now we do not support protocols that don't map all their elements before forking
    usedMethods.zip(graphInfo).foreach { case (method, info) =>
      assert(method.fullName == info.name)
      if(!info.mapInputsBeforeCommit && info.instances.size > 1) {
        // this can be fixed, but requires us to duplicate the state and the method implementation
        // for every instance of the protocol
        throw new NotImplementedError(s"Cannot compile the protocol for ${method.fullName}" +
          " since it does not map all its arguments before forking.")
      }
    }

    // connect to global reset
    val resetInput = List((untimed.name + ".reset") -> reset)

    val inputs = usedMethods.zip(graphInfo).flatMap { case (method, info) =>
      assert(method.fullName == info.name)
      // connect the enable (aka commit) signals, since we know that only one protocol can commit at a time,
      // a simple disjunction is enough
      val enabled = (method.fullIoName + "_enabled") ->
        smt.BVOr(info.instances.map(i => methodSignal(method, i, "Commit")))

      val args = method.args.map { case (name, bits) =>
        val values = info.instances.map(i => smt.BVSymbol(name + "$" + i, bits))
        // if there are multiple instances, we pick the argument of the one that has not committed yet
        val hasNotCommitted = info.instances.drop(1).map(i => methodSignal(method, i, "HasNotCommitted"))
        name -> hasNotCommitted.zip(values.tail)
          .foldLeft[smt.BVExpr](values.head){ case (prev, (en, other)) => smt.BVIte(en, other, prev) }
      }

      List(enabled) ++ args
    } ++ ignoredMethods.flatMap { method =>
      // for unused methods, we just tie off the inputs
      val enabled = (method.fullIoName + "_enabled") -> smt.False()
      val args = method.args.map { case (name, bits) =>  name -> smt.BVLiteral(0, bits) }
      List(enabled) ++ args
    } ++ resetInput

    val connectedInputs = mc.TransitionSystem.connect(untimed.sys, inputs.toMap)

    // the guards do not need to be changed since they are only ever read at the start of a new method
    // when other methods have already committed their state updates
    // the return values however might need to be cached if there is more than one instance
    // of the protocol and the return values are read after the protocol has committed
    val outputs = usedMethods.zip(graphInfo).flatMap { case (method, info) =>
      assert(method.fullName == info.name)
      method.ret.flatMap { case (name, bits) =>
        val ret = smt.BVSymbol(name, bits)
        // trivial case
        if(!info.readAfterCommit) {
          info.instances.map { i =>
            // we can use the same return signal for any instance since none of them will be using it at the same time
           (mc.Signal(name + "$" + i, ret, mc.IsOutput), None)
          }
        } else {
          assert(info.mapInputsBeforeCommit)
          // since the inputs are available when we commit, we can save the output at that point in time
          // and later use the cached version
          info.instances.map { i =>
            val hasCommitted = methodSignal(method, i, "HasCommitted")
            val prev = smt.BVSymbol(name + "$" + i +"$prev", bits)
            val signal = mc.Signal(name + "$" + i, smt.BVIte(hasCommitted, prev, ret), mc.IsOutput)
            val state = mc.State(prev, next = Some(signal.toSymbol), init = None)
            (signal, Some(state))
          }
        }
      }
    }
    val outputState = outputs.flatMap(_._2)
    val outputSignals = outputs.map(_._1)

    val withOutputs = connectedInputs.copy(
      signals = connectedInputs.signals ++ outputSignals,
      states = connectedInputs.states ++ outputState
    )

    //println()
    //println("Inputs:")
    //inputs.foreach(println)
    //println()
    //println("Outputs:")
    //outputSignals.foreach(println)
    //outputState.foreach(println)
    //println()

    //println("Untimed")
    //println(withOutputs.serialize)

    withOutputs
  }

  private def methodSignal(method: MethodInfo, instance: Int, name: String): smt.BVSymbol =
    smt.BVSymbol(method.fullName + "$" + instance + "_" + name, 1)
}
