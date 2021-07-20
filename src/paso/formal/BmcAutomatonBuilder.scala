// Copyright 2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.formal

import maltese.{mc, smt}
import paso.protocols._
import chisel3._
import chisel3.experimental._
import chisel3.util._
import firrtl.annotations.PresetAnnotation

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
    val maxInstances = determineMaxInstances(protos)


    ???
  }

  private def pc(p: Proto, i: Int): smt.BVExpr = {

  }


  /**  finds an upper bound for the maximum number of protocol instances that could be active at the same time */
  private def determineMaxInstances(protos: Seq[Proto]): Seq[Int] = {
    val maxMinCycles = protos.map(_.graph).map(ForkAnalysis.run)
    maxMinCycles.map { case ForkAnalysis.Result(minCyclesToFork, maxCyclesAfterFork) =>
      // TODO: check this formula
      scala.math.ceil(maxCyclesAfterFork.toDouble / minCyclesToFork.toDouble).toInt + 1
    }
  }
}


private class BmcAutomaton(protos: Seq[Proto], instances: Seq[Int]) extends Module with RequireAsyncReset {
  require(protos.nonEmpty)
  require(protos.size == instances.size)
  require(instances.forall(_ > 0))

  annotate(new ChiselAnnotation {
    override def toFirrtl = PresetAnnotation(reset.toTarget)
  })

  // declare I/Os to/from the untimed module
  case class MethodIO(guard: Bool, enable: Bool, args: Seq[UInt], rets: Seq[UInt])
  val methods = protos.map { p =>
    val prefix = p.name + "_"
    val enable = IO(Output(Bool())).suggestName(prefix + "enable")
    enable := false.B
    MethodIO(
      IO(Input(Bool())).suggestName(prefix + "guard"),
      enable,
      p.info.args.map{ case (n,b) => IO(Output(UInt(b.W))).suggestName(prefix + n) }.toSeq,
      p.info.rets.map{ case (n,b) => IO(Input(UInt(b.W))).suggestName(prefix + n) }.toSeq,
    )
  }

  // forking off a new protocol
  val forking = Wire(Bool())
  when(forking) {
    // check which protocols can be executed
    val guards = Cat(methods.map(_.guard))

    // at least one protocol needs to be able to be executed
    verification.assert(guards.orR(), "No guard enabled! Deadlock!")

    // pick an active protocol
    val starting = if(protos.size == 1) { 1.U(1.W) } else {
      val pick = IO(Input(UInt(log2Ceil(protos.size).W))).suggestName("pickProtocol")
      verification.assume(pick < protos.size.U, "Protocol id needs to be in range")
      pick
    }
    // the protocol that was picked should be active
    verification.assume((UIntToOH(starting) & guards) =/= 0.U, "Picked protocol is active!")

    // execute the transaction that we picked
    methods.zipWithIndex.foreach { case (m, i) => m.enable := starting === i.U }



  }


  // generate registers for all protocol instances
  case class ProtoState(p: Proto, i: Int, pc: UInt, args: Seq[UInt], rets: Seq[UInt])
  val states = protos.zip(instances).flatMap { case (proto, inst) =>
    val pcBits = List(log2Ceil(proto.graph.nodes.size), 1).max
    (0 until inst).map { i =>
      val prefix = s"${proto.name}_${i}_"
      val key = (proto.name, i)
      val states =ProtoState(proto, i,
         pc = RegInit(0.U(pcBits.W)).suggestName(prefix + "pc"),
         args = proto.info.args.map{ case (n, b) => Reg(UInt(b.W)).suggestName(prefix + n) }.toSeq,
         rets = proto.info.rets.map{ case (n, b) => Reg(UInt(b.W)).suggestName(prefix + n) }.toSeq,
      )


      key -> states
    }
  }.toMap

  // we are in a fork state if this is the first cycle (i.e. no protocols are active)
  // or if any of the protocols wants to fork
  val noProtocolActive = states.values.map(_.pc === 0.U).reduce(_ && _)




}

private abstract class Builder {

}