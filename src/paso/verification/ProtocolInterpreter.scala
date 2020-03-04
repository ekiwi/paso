// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import uclid.smt
import scala.collection.mutable

class ProtocolInterpreter {
  private trait Phase {}
  private case class InputPhase(edges: Seq[MInputEdge]) extends Phase
  private case class OutputPhase(edges: Seq[MOutputEdge]) extends Phase
  private val _init = MPendingInputNode(mutable.ArrayBuffer(MInputEdge()))
  private var phase: Phase = InputPhase(Seq(_init.next.head))
  private def inInputPhase: Boolean = phase.isInstanceOf[InputPhase]
  private def inOutputPhase: Boolean = phase.isInstanceOf[OutputPhase]
  private def eq(a: smt.Expr, b: smt.Expr): smt.Expr = smt.OperatorApplication(smt.EqualityOp, List(a,b))
  /** Keeps track of which bits of a variable have been mapped */
  private val mappedBits = mutable.HashMap[String, BigInt]()
  //private def isNewMapping() // TODO

  def getGraph: PendingInputNode = _init.toImmutable

  private def isMapping(name: String, hi: Int, lo: Int): Boolean = {
    val oldMap : BigInt = mappedBits.getOrElse(name, 0)
    val mask = (BigInt(1) << (hi - lo + 1)) - 1
    val newMap = mask << lo
    val duplicateBits = oldMap & newMap
    val isMapping = duplicateBits == 0
    if(!isMapping) {
      assert(duplicateBits == newMap, "TODO: deal with mixed new/old assignment")
    }
    mappedBits(name) = oldMap | newMap
    isMapping
  }

  private def isConstraintNotMapping(rhs: smt.Expr): Boolean = rhs match {
    case smt.OperatorApplication(smt.BVExtractOp(hi, lo), List(smt.Symbol(name, typ))) => !isMapping(name, hi, lo)
    case smt.Symbol(name, smt.BoolType) => !isMapping(name, 0, 0)
    case smt.Symbol(name, smt.BitVectorType(w)) => !isMapping(name, w-1, 0)
    case smt.BitVectorLit(value, width) => true
    case smt.BooleanLit(value) => true
    case other => throw new RuntimeException(s"Unexpected rhs expression: $other")
  }


  def onSet(lhs: smt.Expr, rhs: smt.Expr): Unit = {
    require(inInputPhase, "A step is required before sending inputs.")
    val iPhase = phase.asInstanceOf[InputPhase]
    val I_not_A = isConstraintNotMapping(rhs)
    if(I_not_A) iPhase.edges.foreach{_.I.append(eq(lhs, rhs))}
    else        iPhase.edges.foreach{_.A.append(eq(lhs, rhs))}
  }

  def onExpect(lhs: smt.Expr, rhs: smt.Expr): Unit = {
    val oPhase = finishInputPhase()
    val O_not_R = isConstraintNotMapping(rhs)
    if(O_not_R) oPhase.edges.foreach{_.O.append(eq(lhs, rhs))}
    else        oPhase.edges.foreach{_.R.append(eq(lhs, rhs))}
  }

  private def finishInputPhase(): OutputPhase = {
    val new_phase  = phase match {
      case InputPhase(edges) =>
        // finish input phase
        val out_edges = edges.map { in =>
          val state = MPendingOutputNode(mutable.ArrayBuffer(MOutputEdge()))
          assert(in.next.isEmpty)
          in.next = Some(state)
          state.next.head
        }
        OutputPhase(out_edges)
      case o : OutputPhase => o
    }
    phase = new_phase
    // after finishing the input phase we are always in a output phase
    assert(inOutputPhase)
    new_phase
  }

  def onStep(): Unit = {
    phase match {
      case InputPhase(_) =>
        finishInputPhase()
        onStep()
      case OutputPhase(edges) =>
        val in_edges = edges.map { out =>
          val state = MPendingInputNode(mutable.ArrayBuffer(MInputEdge()))
          assert(out.next.isEmpty)
          out.next = Some(state)
          state.next.head
        }
        phase = InputPhase(in_edges)
    }
    // after a step we are always in a new input phase
    assert(inInputPhase)
  }
}

// Mutable Version of the Verification Graph
// used for the initial tree creating in the Protocol Interpreter



case class MPendingInputNode(next: mutable.ArrayBuffer[MInputEdge] = mutable.ArrayBuffer()) {
  def toImmutable: PendingInputNode = PendingInputNode(next.map(_.toImmutable))
}
case class MPendingOutputNode(next: mutable.ArrayBuffer[MOutputEdge] = mutable.ArrayBuffer()) {
  def toImmutable: PendingOutputNode = PendingOutputNode(next.map(_.toImmutable))
}
case class MInputEdge(I: mutable.ArrayBuffer[smt.Expr] = mutable.ArrayBuffer(), A: mutable.ArrayBuffer[smt.Expr] = mutable.ArrayBuffer(), var next: Option[MPendingOutputNode] = None){
  def toImmutable: InputEdge = InputEdge(I, A, next.map(_.toImmutable))
}
case class MOutputEdge(O: mutable.ArrayBuffer[smt.Expr] = mutable.ArrayBuffer(), R: mutable.ArrayBuffer[smt.Expr] = mutable.ArrayBuffer(), var next: Option[MPendingInputNode] = None){
  def toImmutable: OutputEdge = OutputEdge(O, R, next.map(_.toImmutable))
}


// TODO: turn into reverse version (i.e. prev instead of next)
//case class RPendingInputNode(prev: Option[ROutputEdge])
//case class RPendingOutputNode(prev: Option[RInputEdge])
//case class RInputEdge(prev: Option[RPendingInputNode])
//case class ROutputEdge(prev: Option[RPendingOutputNode])
