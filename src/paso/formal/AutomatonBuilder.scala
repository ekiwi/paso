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

  def run(untimed: UntimedModel, info: Seq[ProtocolInfo], protocols: Iterable[UGraph]): mc.TransitionSystem = {
    val prefix = untimed.sys.name + ".automaton."
    val (cfgAuto, graphInfo) = buildControlAutomaton(prefix, info, protocols)


    //println("==============")
    //println("New Automaton:")
    //println("==============")
    //println(auto.serialize)
    //println()

    val utAuto = connectUntimed(untimed, graphInfo)

    // combine control flow automaton and modified untimed spec
    val combined = mc.TransitionSystem.combine(utAuto.name, List(cfgAuto, utAuto))
    TopologicalSort.run(combined)
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

    val prefixArgsPass = new PrefixArgs(info)
    val prefixedProtocols = taggedProtocols.zip(info).map { case(p, i) =>
      prefixArgsPass.run(new PrefixSignals(i.name + "$0_", Set("fork")).run(p))
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
    assert(commitInfo.size == protocolInstances.size)
    val graphInfo = commitInfo.zip(protocolInstances).map { case (c, i) =>
      ProtoGraphInfo(c.readAfterCommit, c.mapInputsBeforeCommit, i)
    }.toSeq

    // many signals end up being the same expression:
    (ReplaceExpressionsWithSignals.run(auto), graphInfo)
  }

  private case class ProtoGraphInfo(readAfterCommit: Boolean, mapInputsBeforeCommit: Boolean, instances: Seq[Int])

  private def connectUntimed(untimed: UntimedModel, graphInfo: Seq[ProtoGraphInfo]): mc.TransitionSystem = {
    require(graphInfo.length == untimed.methods.length)

    // for now we do not support protocols that don't map all their elements before forking
    untimed.methods.zip(graphInfo).foreach { case (method, info) =>
      if(!info.mapInputsBeforeCommit && info.instances.size > 1) {
        // this can be fixed, but requires us to duplicate the state and the method implementation
        // for every instance of the protocol
        throw new NotImplementedError(s"Cannot compile the protocol for ${method.fullName}" +
          " since it does not map all its arguments before forking.")
      }
    }

    // connect to global reset
    val resetInput = List((untimed.name + ".reset") -> smt.BVSymbol("reset", 1))

    val inputs = untimed.methods.zip(graphInfo).flatMap { case (method, info) =>
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
    } ++ resetInput

    val connectedInputs = mc.TransitionSystem.connect(untimed.sys, inputs.toMap)

    // the guards do not need to be changed since they are only ever read at the start of a new method
    // when other methods have already committed their state updates
    // the return values however might need to be cached if there is more than one instance
    // of the protocol and the return values are read after the protocol has committed
    val outputs = untimed.methods.zip(graphInfo).flatMap { case (method, info) =>
      method.ret.flatMap { case (name, bits) =>
        val ret = smt.BVSymbol(name, bits)
        // trivial case
        if(!info.readAfterCommit || info.instances.size == 1) {
          List((mc.Signal(name + "$0", ret, mc.IsOutput), None))
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
