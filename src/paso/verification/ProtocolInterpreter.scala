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



  def onSet(lhs: smt.Expr, rhs: smt.Expr): Unit = {
    require(inInputPhase, "A step is required before sending inputs.")
    val iPhase = phase.asInstanceOf[InputPhase]

    val I_not_A = rhs match {
      case smt.OperatorApplication(smt.BVExtractOp(hi, lo), List(smt.Symbol(name, typ))) => false
      case smt.Symbol(name, typ) => false
      case smt.BitVectorLit(value, width) => true
      case smt.BooleanLit(value) => true
      case other => throw new RuntimeException(s"Unexpected rhs expression: $other")
    }

    if(I_not_A) iPhase.edges.foreach{_.I.append(eq(lhs, rhs))}
    else        iPhase.edges.foreach{_.A.append(eq(lhs, rhs))}
  }

  def onExpect(lhs: smt.Expr, rhs: smt.Expr): Unit = {
    finishInputPhase()


  }

  private def finishInputPhase(): Unit = {
    phase match {
      case InputPhase(edges) =>
        // finish input phase
        val out_edges = edges.map { in =>
          val state = MPendingOutputNode(mutable.ArrayBuffer(MOutputEdge()))
          assert(in.next.isEmpty)
          in.next = Some(state)
          state.next.head
        }
        phase = OutputPhase(out_edges)
      case OutputPhase(_) => None
    }
    // after finishing the input phase we are always in a output phase
    assert(inOutputPhase)
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
