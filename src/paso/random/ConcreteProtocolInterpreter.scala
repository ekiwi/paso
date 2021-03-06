// Copyright 2020-2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.random

import maltese.smt
import paso.protocols._
import treadle.TreadleTester
import firrtl.ir

import scala.collection.mutable



trait TestGuide {
  def chooseTransaction(enabled: IndexedSeq[Proto]): Proto
  def chooseArg(name: String, bits: Int): BigInt
  def chooseInput(name: String, bits: Int): BigInt
}


class ConcreteProtocolInterpreter(untimed: TreadleTester, protocols: IndexedSeq[Proto], impl: TreadleTester, guide: TestGuide, inputs: Seq[(String, Int)]) {
  require(protocols.map(_.name).toSet.size == protocols.size)
  private val stickyInputs = protocols.head.info.stickyInputs
  assert(protocols.forall(_.stickyInputs == stickyInputs))
  private val protocolNameToId = protocols.map(_.name).zipWithIndex.toMap
  private val inputNameToBits = inputs.toMap
  case class ProtocolContext(values: Map[String, BigInt])
  case class Loc(pid: Int, ctx: ProtocolContext, nodeId: Int)

  private def isEnabled(t: ProtocolInfo): Boolean = untimed.peek(t.methodPrefix + "guard") == 1

  // choose a new transaction, execute it and return the new context
  private def fork(): Loc = {
    // pick an enabled transaction
    val enabled = protocols.filter(p => isEnabled(p.info))
    assert(enabled.nonEmpty, "No enabled transactions! Deadlock detected!")
    val next = guide.chooseTransaction(enabled)

    // execute the transaction on the untimed model
    val ctx = executeTransaction(next.info)

    // put it into the list of active transactions
    val pid = protocolNameToId(next.name)
    Loc(pid, ctx, 0)
  }

  // execute a transaction on the untimed model
  private def executeTransaction(t: ProtocolInfo): ProtocolContext = {
    assert(isEnabled(t), s"Cannot execute transaction ${t.name} since its guard is false!")

    // pick args
    val args = t.args.map { case (name, bits) => name -> guide.chooseArg(name, bits) }

    // execute transaction
    args.foreach { case (name, value) => untimed.poke(name, value) }
    val rets = t.rets.map { case(name, _) => name -> untimed.peek(name) }
    untimed.poke(t.methodPrefix + "enabled", 1)
    untimed.step()
    untimed.poke(t.methodPrefix + "enabled", 0)

    // println(s"${t.name}(${args.mkString(", ")}) -> ${rets.mkString(", ")}")

    ProtocolContext(args ++ rets)
  }

  // execute a step of all active protocols
  def executeStep(active: List[Loc]): List[Loc] = {
    // randomize all inputs to the dut if we aren't doing sticky inputs
    if(!stickyInputs) {
      inputs.foreach { case (name, bits) =>
        impl.poke(name, guide.chooseInput(name, bits))
      }
    }

    // if there are no active protocols start one
    val didFork = active.isEmpty
    val atLeastOneActive = if(active.nonEmpty) active else List(fork())

    // we track inputs that have been assigned explicitly by the protocols
    val assignments = new Assignments()

    val nextAndFork = atLeastOneActive.map(executeStep(_, assignments))

    // we can only fork once per cycle
    val forks = nextAndFork.filter(_._2).map(_._1)
    assert(!didFork || forks.isEmpty, s"Cannot fork before first step! $forks")
    assert(forks.size < 2, s"Multiple protocols should never fork in the same step! $forks")

    // if we have a protocol that wants to fork we need to fork an execute the new one
    val forkNext = if(forks.nonEmpty) {
      val (next, forkForked) = executeStep(fork(), assignments)
      assert(!forkForked, s"Cannot fork before first step! $next")
      next
    } else { None }

    val allNext = nextAndFork.flatMap(_._1) ++ forkNext
    allNext
  }

  private case class Assignment(input: String, value: BigInt, info: ir.Info)
  private type Assignments = mutable.HashMap[String, Assignment]

  // execute a step in a single protocol
  private def executeStep(l: Loc, assignments: Assignments): (Option[Loc], Boolean) = {
    val proto = protocols(l.pid)
    implicit val ctx: EvalCtx = EvalCtx(l.ctx, assignments.get)

    var nodeId = l.nodeId
    var didFork = false
    var didStep = false

    while(!didStep) {
      // execute actions in the current state
      val node = proto.graph.nodes(nodeId)
      node.actions.foreach { case UAction(a, info, guard) =>
        assert(guard == smt.True(), "Actions should not have guards for concrete execution!")
        a match {
          case ASignal("fork") => didFork = true
          case ASignal(name) => println(s"WARN: unhandled signal: $name")
          case ASet(input, rhs, isSticky) =>
            // TODO: take stickyness into account
            assert(inputNameToBits.contains(input), s"Unknown input $input! ${inputs.mkString(", ")}")
            assign(input, eval(rhs), info, assignments)
          case AUnSet(input) =>
            assert(inputNameToBits.contains(input), s"Unknown input $input! ${inputs.mkString(", ")}")
            assignments.remove(input)
            impl.poke(input, guide.chooseInput(input, inputNameToBits(input)))
          case AAssert(cond) =>
            val value = eval(cond)
            val failed = value != 1
            assert(!failed, s"Failed assertion from $info: $cond")
          case _: AInputAssign =>
          case _: AMapping => throw new RuntimeException("Unexpected argument mapping! Not supported for concrete execution!")
        }
      }

      // pick a next state
      val activeEdges = node.next.filter(e => eval(e.guard) == 1)
      // we want exact one next state since we are doing concrete execution!
      assert(activeEdges.nonEmpty, s"No active edge from state ${node.name} in protocol ${proto.name}")
      assert(activeEdges.length < 2, s"Multiple active edge from state ${node.name} in protocol ${proto.name}")

      didStep = activeEdges.head.isSync
      nodeId = activeEdges.head.to
    }


    val nextNode = proto.graph.nodes(nodeId)
    val next = if(nextNode.next.nonEmpty) Some(l.copy(nodeId = nodeId)) else None
    (next, didFork)
  }

  private def assign(input: String, value: BigInt, info: ir.Info, assignments: Assignments): Unit = {
    // ensure there are no conflicting assignments in the same cycle
    assignments.get(input) match {
      case Some(Assignment(input, oldValue, oldInfo)) =>
        assert(oldValue == value,
          s"Cannot assign $value @ ${info.serialize}, since $input was previously assigned to $oldValue @ ${oldInfo.serialize} in the same cycle!")
      case None =>
    }
    assignments.put(input, Assignment(input, value, info))
    // execute assignment
    impl.poke(input, value)
  }

  private case class EvalCtx(p: ProtocolContext, getAssignment: String => Option[Assignment]) extends smt.SMTEvalCtx {
    override def getBVSymbol(name: String): BigInt = {
      def isInput = inputNameToBits.contains(name)
      val value = p.values.get(name) match {
        case Some(value) => value
        case None =>
          if(isInput) {
            getAssignment(name).map(_.value).getOrElse(
              throw new RuntimeException(s"Cannot read from input $name since it has not been assigned!"))
          } else {
            impl.peek(name)
          }
      }
      // println(s"$name: $value")
      value
    }
    // the bellow methods should never be executed!
    override def getArraySymbol(name: String) = ???
    override def startVariableScope(name: String, value: BigInt): Unit = ???
    override def endVariableScope(name: String): Unit = ???
    override def constArray(indexWidth: Int, value: BigInt) = ???
  }

  private def eval(e: smt.BVExpr)(implicit ctx: EvalCtx): BigInt = smt.SMTExprEval.eval(e)
}
