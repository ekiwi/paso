// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import paso.chisel.{SMTSimplifier, SMTHelper, SMTHelpers}
import uclid.smt

import scala.collection.mutable


case class ProtocolState(
  name: String = "",                           // for debugging
  isEmpty: Boolean = true,                     // new states are empty until the first set/expect
  parent: Option[ProtocolState] = None,        // prior protocol state
  inputs: Map[smt.Symbol, smt.Expr] = Map(),   // expressions that are applied to the inputs of the DUV
  outputs: Map[smt.Symbol, smt.Expr] = Map(),  // expected outputs of the DUV
  stickyInput: Set[smt.Symbol] = Set(),        // "sticky" inputs retain their value after a step
  pathCondition: Option[smt.Expr] = None       // path condition from the current step, should only depend on outputs
  ) {
  override def toString: String = if(name.isEmpty) super.toString else s"ProtocolState($name)"
}


class ProtocolInterpreter(enforceNoInputAfterOutput: Boolean, val debugPrint: Boolean = false) extends SMTHelpers {
  protected var activeStates: Seq[ProtocolState] = Seq(ProtocolState("0"))
  protected var stateCounter: Int = 1
  protected def getStateName: String = { val i = stateCounter ; stateCounter += 1; i.toString }

  ///////// Single State Update Functions
  def set(state: ProtocolState, input: smt.Symbol, expr: smt.Expr, sticky: Boolean): ProtocolState = {
    if (enforceNoInputAfterOutput) {
      assert(state.outputs.isEmpty, s"Cannot assign to input $input := $expr after calling expect and before calling step")
    }
    val stickyInput = if(sticky) state.stickyInput + input else state.stickyInput - input
    state.copy(isEmpty = false, inputs = state.inputs + (input -> expr), stickyInput=stickyInput)
  }

  def expect(state: ProtocolState, output: smt.Symbol, expr: smt.Expr): ProtocolState =
    state.copy(isEmpty = false, outputs = state.outputs + (output -> expr))

  def fork(state: ProtocolState, cond: smt.Expr): Seq[ProtocolState] = {
    // TODO: check if path condition is sat and prune if it is not
    val tru = state.pathCondition.map(and(_, cond)).getOrElse(cond)
    val fals = state.pathCondition.map(and(_, not(cond))).getOrElse(not(cond))
    Seq(state.copy(isEmpty = false, name=getStateName, pathCondition = Some(tru)),
        state.copy(isEmpty = false, name=getStateName, pathCondition = Some(fals)))
  }

  def step(state: ProtocolState): ProtocolState = {
    // copy sticky inputs to next state
    val inputs = state.stickyInput.toIterator.flatMap(i => state.inputs.get(i).map(i -> _)).toMap

    ProtocolState(
      name = getStateName,
      isEmpty = true,
      parent = Some(state),
      inputs = inputs,
      outputs = Map(),
      stickyInput = state.stickyInput,
      pathCondition = None
    )
  }


  ///////// Callbacks
  def onWhen(cond: smt.Expr, visitTrue: () => Unit, visitFalse: () => Unit): Unit = {
    val simpleCond = SMTSimplifier.simplify(cond)
    val trueFalseStates = activeStates.map(fork(_, simpleCond)).transpose

    // visit true branch
    activeStates = trueFalseStates(0)
    if(debugPrint) println(s"WHEN $cond (${activeStates})")
    visitTrue()
    val finalTrueStates = activeStates
    if(debugPrint) println(s" -> (${activeStates})")

    // visit false branch
    activeStates = trueFalseStates(1)
    if(debugPrint) println(s"WHEN !$cond (${activeStates})")
    visitFalse()
    val finalFalseStates = activeStates
    if(debugPrint) println(s" -> (${activeStates})")

    // combine
    activeStates = finalTrueStates ++ finalFalseStates
  }

  def onSet(lhs: smt.Expr, rhs: smt.Expr, sticky: Boolean = false): Unit = lhs match {
    case s: smt.Symbol =>
      if(debugPrint) println(s"SET $lhs := $rhs (${activeStates})")
      val simpleRhs = SMTSimplifier.simplify(rhs)
      activeStates = activeStates.map(set(_, s, simpleRhs, sticky))
    case other => throw new RuntimeException(s"Cannot assign to $other")
  }

  /** mark an input as don't care */
  def onUnSet(lhs: smt.Symbol): Unit = {
    if(debugPrint) println(s"SET $lhs := DontCare (${activeStates})")
    def unset(state: ProtocolState): ProtocolState = {
      val stickyInput = state.stickyInput - lhs
      val inputs = state.inputs - lhs
      state.copy(inputs=inputs, stickyInput=stickyInput)
    }
    activeStates = activeStates.map(unset)
  }

  def onExpect(lhs: smt.Expr, rhs: smt.Expr): Unit = lhs match {
    case s: smt.Symbol =>
      if(debugPrint) println(s"EXPECT $lhs = $rhs (${activeStates})")
      val simpleRhs = SMTSimplifier.simplify(rhs)
      activeStates = activeStates.map(expect(_, s, simpleRhs))
    case other => throw new RuntimeException(s"Cannot read from $other")
  }

  def onStep(): Unit = {
    if(debugPrint) println(s"STEP (${activeStates})")
    activeStates = activeStates.map(step)
  }

  ///////// State Tree to Graph
  type State = ProtocolState
  private def merge[K,V](a: Map[K, Set[V]],b: Map[K, Set[V]]): Map[K, Set[V]] = {
    (a.toSeq ++ b.toSeq).groupBy(_._1).mapValues(_.flatMap(_._2).toSet)
  }
  private def reverseConnectivity(states: Iterable[State]): (Map[State, Set[State]], Set[State]) = {
    if(states.isEmpty) return (Map(), Set())
    // TODO: this method is probably suboptimal, visiting asymptotically more nodes than necessary
    val parentToChildren = states.filter(_.parent.isDefined).groupBy(_.parent.get).mapValues(_.toSet)
    val roots = states.filter(_.parent.isEmpty).toSet
    val (parentMap, parentRoots) = reverseConnectivity(parentToChildren.keys)
    (merge(parentToChildren, parentMap), roots | parentRoots)
  }

  private def makeGraph(methods: Set[String], states: Iterable[State], children: Map[State, Iterable[State]], mappedBits: BitMap): StepNode = {
    assert(states.forall(_.inputs == states.head.inputs), "states should only differ in their outputs / pathCondition")
    // if we are at a final step
    if(states.head.isEmpty && !children.contains(states.head)) {
      assert(states.forall(s => s.isEmpty && !children.contains(s)))
      return StepNode(Seq(), methods)
    }

    val (inMap, inConst, inBits) = findMappingsAndConstraints(destructEquality(states.head.inputs), mappedBits)

    val outputs = states.map { st =>
      val (outMap, outConst, outBits) = findMappingsAndConstraints(destructEquality(st.outputs), inBits)
      val next = children.get(st).map(c => makeGraph(methods, c, children, outBits)).toSeq
      OutputNode(next, methods, outConst ++ st.pathCondition.toSeq, outMap)
    }.toSeq

    val inputs = Seq(InputNode(outputs, methods, inConst, inMap))
    StepNode(inputs, methods)
  }

  def getGraph(method: String): StepNode = {
    checkFinalStates(activeStates)
    // reverse connectivity
    val (children, roots) = reverseConnectivity(activeStates)
    makeGraph(Set(method), roots, children, Map())
  }

  def checkFinalStates(states: Iterable[ProtocolState]) = {
    println("TODO: do some sanity checks like: are all arguments mapped on all paths?")
  }

  ///////// Mapping or Constraint?

  type BitMap = Map[smt.Symbol, BigInt]
  /**
   * If an argument has been mapped before, it now only serves as a constraint.
   */
  private def findMappingsAndConstraints(eq: Iterable[RangeEquality], mappedBits: BitMap): (Seq[ArgumentEq], Seq[smt.Expr], BitMap) = {
    if(eq.isEmpty) return (Seq(), Seq(), mappedBits)

    val newBits = mutable.HashMap(mappedBits.toSeq: _*)

    val mapConst = eq.map {
      case c: ConstantEq => (None, Some(c.toExpr()))
      case a: ArgumentEq =>
        if(isMapping(a.argRange, newBits)) {
          (Some(a), None)
        } else {
          (None, Some(a.toExpr()))
        }
      case other => throw new RuntimeException(s"Unexpected: $other")
    }.toSeq

    val mapping = mapConst.flatMap(_._1)
    val constraints = mapConst.flatMap(_._2)
    (mapping, constraints, newBits.toMap)
  }
  private def isMapping(argRange: Range, newBits: mutable.HashMap[smt.Symbol, BigInt]): Boolean = {
    val oldMap : BigInt = newBits.getOrElse(argRange.sym, 0)
    val mask = (BigInt(1) << argRange.width) - 1
    val newMap = mask << argRange.lo
    val duplicateBits = oldMap & newMap
    val isMapping = duplicateBits == 0
    if(!isMapping) {
      assert(duplicateBits == newMap, "TODO: deal with mixed new/old assignment")
    }
    newBits(argRange.sym) = oldMap | newMap
    isMapping
  }


  /** Turns concatenations of symbols, symbol bit extractions and constants into a sequence of equalities
   *  Example: c = Cat(0b00, Cat(a[1:0], b)) -->
   *           Seq(ConstantEq(c[4:3],0), ArgumentEq(c[2:1], a[1:0]), ArgumentEq(c[0:0], b[0:0]))
   * */
  private def destructEquality(lhs: Range, rhs: smt.Expr): Iterable[RangeEquality] = rhs match {
    case smt.OperatorApplication(smt.BVConcatOp(w), List(a, b)) =>
      val bWidth = getBits(b.typ)
      destructEquality(lhs.copy(lo = lhs.lo + bWidth), a) ++
      destructEquality(lhs.copy(hi = lhs.hi + bWidth), b)
    case s: smt.Symbol => Seq(ArgumentEq(lhs, Range(s, getBits(s.typ)-1, 0)))
    case smt.BooleanLit(v) => Seq(ConstantEq(lhs, if(v) 1 else 0))
    case smt.BitVectorLit(v, _) => Seq(ConstantEq(lhs, v))
    case smt.OperatorApplication(smt.BVExtractOp(hi, lo), List(s: smt.Symbol)) =>
      Seq(ArgumentEq(lhs, Range(s, hi, lo)))
    case other => throw new RuntimeException(s"Unsupported expression $other. Maybe you need to simplify/constant prop more?")
  }
  private def destructEquality(mapping: Map[smt.Symbol, smt.Expr]): Iterable[RangeEquality] = {
    mapping.flatMap{case (sym, expr) => destructEquality(Range(sym, getBits(sym.typ) - 1, 0), expr) }
  }
}

case class Range(sym: smt.Symbol, hi: Int, lo: Int) {
  def symBits: Int = SMTHelper.getBits(sym.typ)
  def isFullRange: Boolean = lo == 0 && hi == (symBits - 1)
  def toExpr(): smt.Expr = if(isFullRange) sym else smt.OperatorApplication(smt.BVExtractOp(hi=hi,lo=lo), List(sym))
  def width: Int = hi - lo + 1
}
trait RangeEquality{ val range: Range ; def toExpr(): smt.Expr }
case class ConstantEq(range: Range, value: BigInt) extends  RangeEquality {
  override def toExpr(): smt.Expr = {
    val const = if(range.width == 1) smt.BooleanLit(value != 0) else smt.BitVectorLit(value, range.width)
    smt.OperatorApplication(smt.EqualityOp, List(range.toExpr(), const))
  }
}
case class ArgumentEq(range: Range, argRange: Range) extends RangeEquality {
  override def toExpr(): smt.Expr = smt.OperatorApplication(smt.EqualityOp, List(range.toExpr(), argRange.toExpr()))
  def toGuardedExpr(): smt.Expr = {
    val guard = smt.Symbol(argRange.sym.id + ".valid", smt.BoolType)
    smt.OperatorApplication(smt.ImplicationOp, List(guard, toExpr()))
  }
}