// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import paso.chisel.{SMTSimplifier, SmtHelpers}
import uclid.smt

import scala.collection.mutable


case class ProtocolState(
  parent: Option[ProtocolState] = None,        // prior protocol state
  inputs: Map[smt.Symbol, smt.Expr] = Map(),   // expressions that are applied to the inputs of the DUV
  outputs: Map[smt.Symbol, smt.Expr] = Map(),  // expected outputs of the DUV
  stickyInput: Set[smt.Symbol] = Set(),        // "sticky" inputs retain their value after a step
  mappedBits: Map[smt.Symbol, BigInt] = Map(), // tracks which bits of arguments and return arguments have already been mapped
  pathCondition: Option[smt.Expr] = None       // path condition from the current step, should only depend on outputs
  )



class ProtocolInterpreter(enforceNoInputAfterOutput: Boolean) extends SmtHelpers {
  protected var activeStates: Seq[ProtocolState] = Seq(ProtocolState())

  ///////// Single State Update Functions
  def set(state: ProtocolState, input: smt.Symbol, expr: smt.Expr): ProtocolState = {
    if (enforceNoInputAfterOutput) {
      assert(state.outputs.isEmpty, s"Cannot assign to input $input := $expr after calling expect and before calling step")
    }
    state.copy(inputs = state.inputs + (input -> expr))
  }

  def expect(state: ProtocolState, output: smt.Symbol, expr: smt.Expr): ProtocolState =
    state.copy(outputs = state.outputs + (output -> expr))

  def fork(state: ProtocolState, cond: smt.Expr): Seq[ProtocolState] = {
    // TODO: check if path condition is sat and prune if it is not
    val tru = state.pathCondition.map(and(_, cond)).getOrElse(cond)
    val fals = state.pathCondition.map(and(_, not(cond))).getOrElse(not(cond))
    Seq(state.copy(pathCondition = Some(tru)), state.copy(pathCondition = Some(fals)))
  }

  def step(state: ProtocolState): ProtocolState = {
    // TODO: find newly mapped bits
    val mappedBits = state.mappedBits

    // copy sticky inputs to next state
    val inputs = state.stickyInput.toIterator.flatMap(i => state.inputs.get(i).map(i -> _)).toMap

    ProtocolState(
      parent = Some(state),
      inputs = inputs,
      outputs = Map(),
      stickyInput = state.stickyInput,
      mappedBits = mappedBits,
      pathCondition = None
    )
  }


  ///////// Callbacks
  def onWhen(cond: smt.Expr, visitTrue: () => Unit, visitFalse: () => Unit): Unit = {
    val simpleCond = SMTSimplifier.simplify(cond)
    val trueFalseStates = activeStates.map(fork(_, simpleCond)).transpose

    // visit true branch
    activeStates = trueFalseStates(0)
    visitTrue()
    val finalTrueStates = activeStates

    // visit false branch
    activeStates = trueFalseStates(1)
    visitFalse()
    val finalFalseStates = activeStates

    // combine
    activeStates = finalTrueStates ++ finalFalseStates
  }

  def onSet(lhs: smt.Expr, rhs: smt.Expr): Unit = lhs match {
    case s: smt.Symbol => activeStates.map(set(_, s, rhs))
    case other => throw new RuntimeException(s"Cannot assign to $other")
  }

  def onExpect(lhs: smt.Expr, rhs: smt.Expr): Unit = lhs match {
    case s: smt.Symbol => activeStates.map(expect(_, s, rhs))
    case other => throw new RuntimeException(s"Cannot read from $other")
  }

  def onStep(): Unit = {
    val newStates = activeStates.map(step)
    activeStates = newStates
  }

  ///////// State Tree to Graph
  type State = ProtocolState
  private def reverseConnectivity(states: Iterable[State]): (Map[State, Iterable[State]], Seq[State]) = {
    val parentToChildren = states.filter(_.parent.isDefined).groupBy(_.parent.get)
    val roots = states.filter(_.parent.isEmpty).toSeq
    val (parentMap, parentRoots) = reverseConnectivity(parentToChildren.keys)
    (parentToChildren ++ parentMap, roots ++ parentRoots)
  }

  private def makeGraph(state: State, children: Map[State, Iterable[State]], guard: Option[smt.Expr]): PendingInputNode = {
    

  }

  def getGraph(method: String, guard: smt.Expr): PendingInputNode = {
    checkFinalStates(activeStates)

    // reverse connectivity
    val (children, roots) = reverseConnectivity(activeStates)
    assert(roots.length == 1, s"Expected to find exactly one starting state, not: $roots")



    // add method guard to the constraints for the first edge
    // --> the first edge should only be executed if our system is in the correct state
    if(guard != smt.BooleanLit(true)) { _init.next.foreach(_.I.append(guard)) }
    _init.toImmutable(method)
  }

  def checkFinalStates(states: Iterable[ProtocolState]) = {
    println("TODO: do some sanity checks like: are all arguments mapped on all paths?")
  }

}

class OldProtocolInterpreter {
  private trait Phase {}
  private case class IdlePhase(states: Seq[MPendingInputNode]) extends Phase
  private case class InputPhase(edges: Seq[MInputEdge]) extends Phase
  private case class OutputPhase(edges: Seq[MOutputEdge], prev: Seq[MPendingOutputNode]) extends Phase
  private val _init = MPendingInputNode(mutable.ArrayBuffer())
  private var phase: Phase = IdlePhase(Seq(_init))
  private def inIdlePhase: Boolean = phase.isInstanceOf[IdlePhase]
  private def inInputPhase: Boolean = phase.isInstanceOf[InputPhase]
  private def inOutputPhase: Boolean = phase.isInstanceOf[OutputPhase]
  private def eq(a: smt.Expr, b: smt.Expr): smt.Expr = smt.OperatorApplication(smt.EqualityOp, List(a,b))
  private def not(e: smt.Expr): smt.Expr = smt.OperatorApplication(smt.NegationOp, List(e))
  /** Keeps track of which bits of a variable have been mapped */
  private val mappedBits = mutable.HashMap[String, BigInt]()
  //private def isNewMapping() // TODO

  def getGraph(method: String, guard: smt.Expr): PendingInputNode = {
    // add method guard to the constraints for the first edge
    // --> the first edge should only be executed if our system is in the correct state
    if(guard != smt.BooleanLit(true)) { _init.next.foreach(_.I.append(guard)) }
    _init.toImmutable(method)
  }

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


  def onWhen(cond: smt.Expr, visitTrue: () => Unit, visitFalse: () => Unit): Unit = {
    val oPhase = finishInputPhase()
    def copyPhase(e: smt.Expr): OutputPhase = {
      val simpl = SMTSimplifier.simplify(e)
      val states = oPhase.prev.map(s => s.copy(next = s.next.map(e => e.copy(O = e.O ++ Seq(simpl)))))
      val edges = states.flatMap(_.next)
      OutputPhase(edges, states)
    }

    // generate a true Phase and a false Phase
    val originalStates = oPhase.prev
    val truePhase = copyPhase(cond)
    val falsePhase = copyPhase(not(cond))

    // execute both sides of the branch
    phase = truePhase
    println(s"WHEN $cond")
    visitTrue()
    val newTruePhase = finishInputPhase()
    phase = falsePhase
    println(s"WHEN ${not(cond)}")
    visitFalse()
    val newFalsePhase = finishInputPhase()

    // merge: this relies on the fact that no new states can be added and Seq is ordered
    assert(newTruePhase.prev.length == newFalsePhase.prev.length)
    val states = originalStates.zip(newTruePhase.prev).zip(newFalsePhase.prev).map { case ((st, sTrue), sFalse) =>
      // edges in sTrue and sFalse should be mutually exclusive
      st.next.clear()
      st.next ++= sTrue.next ++ sFalse.next
      st
    }
    val edges = states.flatMap(_.next)
    phase = OutputPhase(edges, states)
  }


  def onSet(lhs: smt.Expr, rhs: smt.Expr): Unit = {
    println(s"SET: $lhs := $rhs")
    val iPhase = enterInputPhase()
    val simple_rhs = SMTSimplifier.simplify(rhs) // use the SMT Simplifier for constant prop
    val I_not_A = isConstraintNotMapping(simple_rhs)
    if(I_not_A) iPhase.edges.foreach{_.I.append(eq(lhs, simple_rhs))}
    else        iPhase.edges.foreach{_.A.append(eq(lhs, simple_rhs))}
  }

  def onExpect(lhs: smt.Expr, rhs: smt.Expr): Unit = {
    println(s"EXPECT: $lhs == $rhs")
    val oPhase = finishInputPhase()
    val simple_rhs = SMTSimplifier.simplify(rhs) // use the SMT Simplifier for constant prop
    val O_not_R = isConstraintNotMapping(simple_rhs)
    if(O_not_R) oPhase.edges.foreach{_.O.append(eq(lhs, simple_rhs))}
    else        oPhase.edges.foreach{_.R.append(eq(lhs, simple_rhs))}
  }

  private def finishInputPhase(): OutputPhase = {
    val new_phase  = phase match {
      case IdlePhase(_) => enterInputPhase() ; finishInputPhase()
      case InputPhase(edges) =>
        // finish input phase
        val out_states = edges.map { in =>
          val state = MPendingOutputNode(mutable.ArrayBuffer(MOutputEdge()))
          assert(in.next.isEmpty)
          in.next = Some(state)
          state
        }
        OutputPhase(out_states.map(_.next.head), out_states)
      case o : OutputPhase => o
      case other => throw new RuntimeException(s"Unexpected phase: $other")
    }
    phase = new_phase
    // after finishing the input phase we are always in a output phase
    assert(inOutputPhase)
    new_phase
  }

  private def enterInputPhase(): InputPhase = {
    val new_phase = phase match {
      case IdlePhase(states) =>
        val edges = states.map { st => st.next.append(MInputEdge()) ; st.next.head }
        InputPhase(edges)
      case in : InputPhase => in
      case OutputPhase(_, _) =>
        throw new RuntimeException("A step is required before sending inputs.")
    }
    phase = new_phase
    // after finishing the input phase we are always in a output phase
    assert(inInputPhase)
    new_phase
  }

  def onStep(): Unit = {
    println("STEP")
    phase match {
      case IdlePhase(_) =>
        enterInputPhase()
        onStep()
      case InputPhase(_) =>
        finishInputPhase()
        onStep()
      case OutputPhase(edges, _) =>
        val states = edges.map { out =>
          val state = MPendingInputNode(mutable.ArrayBuffer())
          assert(out.next.isEmpty)
          out.next = Some(state)
          state
        }
        phase = IdlePhase(states)
    }
    // after a step we are always in a new idle phase
    assert(inIdlePhase)
  }
}

// Mutable Version of the Verification Graph
// used for the initial tree creating in the Protocol Interpreter



case class MPendingInputNode(next: mutable.ArrayBuffer[MInputEdge] = mutable.ArrayBuffer()) {
  def toImmutable(method: String): PendingInputNode = PendingInputNode(next.map(_.toImmutable(method)))
}
case class MPendingOutputNode(next: mutable.ArrayBuffer[MOutputEdge] = mutable.ArrayBuffer()) {
  def toImmutable(method: String): PendingOutputNode = PendingOutputNode(next.map(_.toImmutable(method)))
}
case class MInputEdge(I: mutable.ArrayBuffer[smt.Expr] = mutable.ArrayBuffer(), A: mutable.ArrayBuffer[smt.Expr] = mutable.ArrayBuffer(), var next: Option[MPendingOutputNode] = None){
  def toImmutable(method: String): InputEdge = InputEdge(I, A, Set(method), next.get.toImmutable(method))
}
case class MOutputEdge(O: mutable.ArrayBuffer[smt.Expr] = mutable.ArrayBuffer(), R: mutable.ArrayBuffer[smt.Expr] = mutable.ArrayBuffer(), var next: Option[MPendingInputNode] = None){
  def toImmutable(method: String): OutputEdge = OutputEdge(O, R, Set(method), next.get.toImmutable(method))
}


// TODO: turn into reverse version (i.e. prev instead of next)
//case class RPendingInputNode(prev: Option[ROutputEdge])
//case class RPendingOutputNode(prev: Option[RInputEdge])
//case class RInputEdge(prev: Option[RPendingInputNode])
//case class ROutputEdge(prev: Option[RPendingOutputNode])
