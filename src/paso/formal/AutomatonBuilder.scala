// Copyright 2020-2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.formal

import maltese.passes.ReplaceExpressionsWithSignals
import maltese.{mc, smt}
import paso.protocols._

import java.nio.file.Path

class AutomatonBuilder(solver: smt.Solver, workingDir: Path) {

  def run(untimed: UntimedModel, info: Seq[ProtocolInfo], protocols: Iterable[UGraph]): Unit = {
    val prefix = untimed.sys.name + ".automaton."
    val (auto, graphInfo) = buildControlAutomaton(prefix, info, protocols)


    println("==============")
    println("New Automaton:")
    println("==============")
    println(auto.serialize)
    println()

    connectUntimed(untimed, graphInfo)
  }

  private def buildControlAutomaton(prefix: String, info: Seq[ProtocolInfo], protocols: Iterable[UGraph]):
  (mc.TransitionSystem, Seq[ProtoGraphInfo]) = {
    // first we check to see when the protocols commit
    val commits = protocols.zip(info).map { case (p, i) =>
      new CommitAnalysis(i.rets).run(p)
    }
    val commitInfo = commits.map(_._2)

    val tagPasses = Seq(new TagInternalNodes("Active"), new TagStartNode("Start"),
      new RemoveEmptyLeafStates(Set("HasCommitted")))
    val taggedProtocols = commits.map(_._1).map { p => tagPasses.foldLeft(p)((old, pass) => pass.run(old)) }

    val prefixedProtocols = taggedProtocols.zip(info).map { case(p, i) =>
      new PrefixSignals(i.name + "$0_", Set("fork")).run(p)
    }

    // trying to make a paso automaton out of u graphs
    val b = new UGraphBuilder("combined")
    val start = b.addNode("start", List(UAction(ASignal("Start"))))
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
    val guardsToAssumptions = new GuardsToAssumptions(gSolver)
    ProtocolVisualization.saveDot(guardsToAssumptions.run(merged), false, s"$workingDir/merged.simpl.dot")

    val forkPass = new ExpandForksPass(info, gSolver, workingDir.toString)
    val forksExpanded = forkPass.run(merged)
    val protocolInstances = forkPass.getProtocolInstances
    ProtocolVisualization.saveDot(forksExpanded, false, s"$workingDir/fork.dot")
    // remove signals that are no longer needed:
    val removeSignals = new RemoveSignalsEndingWith(List("Active", "AllMapped"))
    val simplified = removeSignals.run(guardsToAssumptions.run(forksExpanded))
    ProtocolVisualization.saveDot(simplified, false, s"$workingDir/fork.simpl.dot")

    // make automaton
    val auto = new UGraphToTransitionSystem(gSolver).run(simplified, invert = false, prefix=prefix)

    //println("Protocols:  " + info.map(_.name).mkString(", "))
    //println("CommitInfo: " + commitInfo.toString)
    //println("Instances:  " + protocolInstances)
    val graphInfo = commitInfo.zip(protocolInstances).map { case (c, i) =>
      ProtoGraphInfo(c.readAfterCommit, c.mapInputsBeforeCommit, i)
    }.toSeq

    // many signals end up being the same expression:
    (ReplaceExpressionsWithSignals.run(auto), graphInfo)
  }

  private case class ProtoGraphInfo(readAfterCommit: Boolean, mapInputsBeforeCommit: Boolean, instances: Seq[Int])

  private def connectUntimed(untimed: UntimedModel, graphInfo: Seq[ProtoGraphInfo]): mc.TransitionSystem = {

    println()
    println("Untimed")
    println(untimed.sys.serialize)

    untimed.sys
  }
}
