// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import java.io.FileWriter

import chisel3.util.log2Ceil

import scala.sys.process._
import paso.chisel.{SMTHelpers, SMTSimplifier}
import uclid.smt
import uclid.smt.{BVGTUOp, ConjunctionOp}

import scala.collection.mutable

object VerificationGraph extends SMTHelpers {
  def merge(a: StepNode, b: StepNode): StepNode = {
    // TODO: also consider guards (i.e. protocols can be identical as long as their method guards are mutually exclusive)
    assert(!a.isFork && !b.isFork)
    assert(a.id == 0 && b.id == 0)
    a.next.foreach { aNext =>
      b.next.foreach { bNext =>
        val mutuallyExlusive = Checker.isUnsat(and(aNext.constraintExpr, bNext.constraintExpr))
        assert(mutuallyExlusive, "We currently require all methods to have distinguishing inputs on the first cycle.")
      }
    }
    StepNode(a.next ++ b.next, a.methods | b.methods, 0, isFork = false)
  }

}

case class ForkNode(ii: Int, guard: smt.Expr, method: String)
class VerificationTreeEncoder(check: BoundedCheckBuilder, guards: Map[String, smt.Expr]) extends SMTHelpers {

  case class State(ii: Int, pathGuard: smt.Expr)
  def run(proto: StepNode): Seq[ForkNode] = {
    visit(proto, State(-1, tru))
    forkNodes
  }

  private var branchCounter: Int = 0
  private def getUniqueBranchSymbols(choices: Int): Seq[smt.Symbol] = {
    val base = s"branch_${branchCounter}_c"
    branchCounter += 1
    val names = (0 until choices).map(ii => base + ii.toString)
    names.map(smt.Symbol(_, smt.BoolType))
  }
  private val forkNodes = mutable.ArrayBuffer[ForkNode]()

  private def addForkNode(node: StepNode, state: State): Unit = {
    assert(node.methods.size == 1, "Only a single method allowed in fork node!")
    forkNodes += ForkNode(state.ii, state.pathGuard, node.methods.head)
  }

  private def assumeAt(state: State, e: smt.Expr): Unit = check.assumeAt(state.ii, implies(state.pathGuard, e))
  private def assertAt(state: State, e: smt.Expr): Unit = check.assertAt(state.ii, implies(state.pathGuard, e))

  private def visit(node: StepNode, oldState: State): Unit = {
    val state = oldState.copy(ii = oldState.ii + 1)
    if(node.isFork) { addForkNode(node, state) }
    if(node.isFinal) { return }

    // either of the following input constraints could be true
    val inputConstraints = node.next.map { ii =>
      // add method guard if necessary
      if(ii.methods.size > 1 || ii.methods != node.methods || state.ii == 0) {
        val g = ii.methods.toSeq.map(guards).filterNot(_ == tru)
        if(g.nonEmpty) {
          and(ii.constraintExpr, disjunction(g))
        } else {
          ii.constraintExpr
        }
      } else {
        ii.constraintExpr
      }
    }
    assumeAt(state, disjunction(inputConstraints))

    if(node.isBranchPoint) {
      val syms = getUniqueBranchSymbols(node.next.length)
      node.next.zip(syms).foreach { case (input, sym) =>
        // associate path with a symbol
        check.assumeAt(state.ii, iff(sym, and(state.pathGuard, input.constraintExpr)))
        visit(input, state.copy(pathGuard = sym))
      }
    } else {
      visit(node.next.head, state)
    }
  }

  private def visit(node: InputNode, state: State): Unit = {
    assert(!node.isFinal, "Should never end on an input node. Expecting an empty output node to follow.")
    if(node.mappings.nonEmpty) { check.assumeAt(state.ii, implies(state.pathGuard, node.mappingExpr)) }

    // at least one of the following output constraints has to be true
    assertAt(state,  disjunction(node.next.map(o => and(o.constraintExpr, o.mappingExpr))))

    if(node.isBranchPoint) {
      val syms = getUniqueBranchSymbols(node.next.length)
      node.next.zip(syms).foreach { case (output, sym) =>
        // associate path with a symbol
        check.assumeAt(state.ii, iff(sym, and(state.pathGuard, output.constraintExpr)))
        visit(output, state.copy(pathGuard = sym))
      }
    } else {
      visit(node.next.head, state)
    }
  }

  private def visit(node: OutputNode, state: State): Unit = {
    assert(!node.isFinal, "OutputNodes not followed by a StepNode are no longer supported!")
    assert(!node.isBranchPoint, "Cannot branch on steps! No way to distinguish between steps.")
    visit(node.next.head, state)
  }
}


/**this is the skeleton of a Paso Automaton,
 * encoding the basic FSM without any of the actual constraints, arch state or argument mappings
 * */
case class PasoFsm(states: Seq[PasoFsmState], edges: Seq[PasoFsmEdge], instances: Map[String, Int])
/** represents a StepNode in a protocol */
case class Loc(proto: String, id: Int, isFork: Boolean, isFinal: Boolean) {
  override def toString: String = proto + "@" + id
}
object Loc { def apply(proto: String, node: StepNode): Loc = Loc(proto, node.id, node.isFork, node.isFinal) }
/** represents a StepNode in a specific instance of a protocol */
case class InstanceLoc(instance: Int, loc: Loc) {
  override def toString: String = loc.proto + "'" + instance + "@" + loc.id
}
case class PasoFsmState(id: Int, active: Seq[InstanceLoc], isFork: Boolean, choices: Seq[InstanceLoc]) {
  require(!isFork || choices.nonEmpty, "Forks must contain all possible first steps!")
  require(choices.forall(_.loc.id == 0), "Choices should only contain first steps!")
  override def toString: String = "{" + active.map(_.toString).sorted.mkString(", ") + "}" + (if(isFork) " (F)" else "")
}
case class BranchLoc(branchId: Int, loc: InstanceLoc) {
  override def toString: String = loc.toString + "b" + branchId
}
case class PasoFsmEdge(from: PasoFsmState, to: PasoFsmState, active: Seq[BranchLoc]) {
  override def toString: String = from + " -> " + to + " : {" + active.map(_.toString).sorted.mkString(", ") + "}"
}

case class PasoFsmEncoder(protocols: Map[String, StepNode]) {
  private def findSucessors(node: StepNode): Seq[StepNode] = node.next.flatMap(_.next.flatMap(_.next))
  private def findSteps(node: StepNode): Seq[StepNode] = {
    Seq(node) ++ node.next.flatMap(_.next.flatMap(_.next.flatMap(findSteps)))
  }
  private val nextLoc: Map[Loc, Seq[Loc]] = protocols.flatMap { case (name, step) =>
    findSteps(step).map(s => Loc(name, s) -> findSucessors(s).map(x => Loc(name, x)))
  }
  private val instanceCount = mutable.HashMap(protocols.keys.map(_ -> 0).toSeq: _*)
  private val states = mutable.HashMap[(Set[InstanceLoc], Boolean), PasoFsmState]()
  private val nextState = mutable.ArrayBuffer[PasoFsmEdge]()

  /** returns the id of a free instance of the protocol specified */
  def getFreeInstance(active: Seq[InstanceLoc], proto: String): Int = {
    val activeIds = active.filter(_.loc.proto == proto).map(_.instance).toSet
    val smallestId = (0 until 100).find(ii => !activeIds.contains(ii)).get
    // ensure that the instance count is correct
    if(instanceCount(proto) <= smallestId) instanceCount(proto) = smallestId + 1
    smallestId
  }

  // https://stackoverflow.com/questions/8321906/lazy-cartesian-product-of-several-seqs-in-scala/8569263
  private def product[N](xs: Seq[Seq[N]]): Seq[Seq[N]] =
    xs.foldLeft(Seq(Seq.empty[N])){ (x, y) => for (a <- x.view; b <- y) yield a :+ b }

  private def getForkChoices(active: Seq[InstanceLoc]): Seq[InstanceLoc] = {
    protocols.map { case (proto, step) =>
      val id = getFreeInstance(active, proto)
      InstanceLoc(id, Loc(proto, step))
    }.toSeq
  }


  def executeState(st: PasoFsmState): Unit = {
    // println(s"executeState($st)")

    val newLocs = if(!st.isFork) Seq(Seq()) else st.choices.map(Seq(_))

    newLocs.zipWithIndex.foreach { case (nl, forkId) =>
      // if(nl.nonEmpty) println(s"FORK: ${nl.head}")
      val currentLocs = nl ++ st.active

      // branch ids rely on the fact that nextLoc keeps the order of next steps consistent with the order in the next field of the OutputNode
      val paths = currentLocs.map(loc =>
        nextLoc(loc.loc).zipWithIndex.map{ case (next, branchId) => BranchLoc(branchId, InstanceLoc(loc.instance, next)) }
      )

      // create a new state for every possible path
      product(paths).foreach { nextLocs =>
        val isFork = nextLocs.exists(_.loc.loc.isFork)
        val active = nextLocs.map(_.loc).filterNot(_.loc.isFinal)
        // check if this state already exists
        val key = (active.toSet, isFork)
        val alreadyVisited = states.contains(key)
        val uniqueNext = states.getOrElseUpdate(key, {
          val choices = if(!isFork) Seq() else getForkChoices(active)
          PasoFsmState(states.size, active, isFork, choices)
        })
        // describe the edge
        val e = PasoFsmEdge(st, uniqueNext, nextLocs)
        nextState.append(e)
        if(!alreadyVisited) {
          executeState(uniqueNext)
        }
      }
    }
  }

  // TODO: check that all protocols (including the guard) are mutually exclusive
  def run(): PasoFsm = {
    val initState = PasoFsmState(0, Seq(), isFork = true, getForkChoices(Seq()))
    states((Set(), true)) = initState
    executeState(initState)
    val sts: Seq[PasoFsmState] = states.values.toSeq.sortBy(_.id).toVector
    PasoFsm(sts, nextState, instanceCount.toMap)
  }
}

case class ArgMap(guard: smt.Expr, eq: ArgumentEq)
case class OutputConstraint(guard: smt.Expr, constraint: smt.Expr)
case class NextState(guard: smt.Expr, nextId: Int)
case class StateUpdate(guard: smt.Expr, state: smt.Symbol, value: smt.Expr)
case class PasoState(id: Int,
   inputMappings: Seq[ArgMap], // mapping DUV inputs to method arguments (depending on input constraints)
   environmentAssumptions: smt.Expr, // restrict the inputs space
   nextStates: Seq[NextState], // the next state might depend on inputs and outputs
   systemAssertions: Seq[OutputConstraint], // expected outputs depending on the input path taken
   stateUpdates: Seq[StateUpdate], // updates to the architectural state
  )

object PasoCombinedAutomatonEncoder extends SMTHelpers {
  // TODO: remove simplifications
  private def simplify(e: smt.Expr): smt.Expr = SMTSimplifier.simplify(e)
  private def simplify(e: Seq[smt.Expr]): Seq[smt.Expr] = e.map(SMTSimplifier.simplify).filterNot(_ == tru)

  def run(prefix: String, resetAssumption: smt.Expr, start: PasoState, states: Seq[PasoState], switchAssumesAndGuarantees: Boolean): smt.TransitionSystem = {
    // calculate transition function for the "state" state, i.e. the state of our automaton
    val stateBits = log2Ceil(states.length + 1)
    val stateSym = smt.Symbol(prefix + "state", smt.BitVectorType(stateBits))
    def inState(id: Int): smt.Expr = eq(stateSym, smt.BitVectorLit(id, stateBits))

    // if we ever get into this state, we have done something wrong
    val invalidState = smt.BitVectorLit(states.length, stateBits)
    val badInInvalidState = eq(stateSym, invalidState)

    // calculate the next state
    val nextStateAndGuard= states.flatMap(s => s.nextStates.map(n => (n.nextId, and(n.guard, inState(s.id)))))
    val nextState = nextStateAndGuard.groupBy(_._1).foldLeft[smt.Expr](invalidState){ case (other, (stateId, guards)) =>
      ite(disjunction(guards.map(_._2)), smt.BitVectorLit(stateId, stateBits), other)
    }
    val stateState = smt.State(stateSym, init = Some(smt.BitVectorLit(start.id, stateBits)), next = Some(simplify(nextState)))

    // besides the "state" we need to keep track of argument mapped in earlier cycles
    // so that we can use them in output constraints in a later cycle
    // to do this we create a state for every argument
    val mappingsByArgName = states.flatMap(s => s.inputMappings.map((s.id,_))).groupBy(_._2.eq.argRange.sym.id)
    val args = mappingsByArgName.map { case(_, m) =>
      val stateSym = m.head._2.eq.argRange.sym
      val nextArg = m.groupBy(_._1).map { case (state, updates) =>
        // TODO: for now we only support a single full update --> need to implement partial updates at some point
        assert(updates.length == 1)
        assert(updates.head._2.eq.argRange.isFullRange)
        and(inState(state), updates.head._2.guard) -> updates.head._2.eq.range.toExpr()
      }.foldLeft[smt.Expr](stateSym){ case (other, (cond, value)) => ite(cond, value, other) }
      smt.State(stateSym, next = Some(simplify(nextArg)))
    }

    // we also need to keep track of the architectural state of the untimed model
    val updatesByState = states.flatMap(s => s.stateUpdates.map((s.id, _))).groupBy(_._2.state.id)
    val untimedState = updatesByState.map { case (_, u) =>
      val stateSym = u.head._2.state
      val nextState = u.map { case (state, update) =>
        and(inState(state), update.guard) -> update.value
      }.foldLeft[smt.Expr](stateSym){ case (other, (cond, value)) => ite(cond, value, other) }
      smt.State(stateSym, next = Some(simplify(nextState)))
      // TODO: add option to init the state (for bmc)
    }

    val assumptions = states.map(s => implies(inState(s.id), s.environmentAssumptions)) ++ Seq(resetAssumption)
    val guarantees = states.flatMap(s => s.systemAssertions.map(a => implies(inState(s.id), implies(a.guard, a.constraint))))

    val assumptionsSimple = simplify(assumptions)
    val guaranteesSimple  = simplify(guarantees)

    // turn environment assumptions or system assertions into constraints
    val constraints = if(switchAssumesAndGuarantees) guaranteesSimple else assumptionsSimple

    // turn system assertions or environment assumptions into bad states (requires negation)
    val asserts = if(switchAssumesAndGuarantees) assumptionsSimple else guaranteesSimple
    val bads = asserts.map(not)

    smt.TransitionSystem(
      name = Some(prefix.dropRight(1)),
      inputs = Seq(),
      states = Seq(stateState) ++ args ++ untimedState,
      constraints = constraints,
      bad = Seq(badInInvalidState) ++ bads
    )
  }
}

object DuplicateProtocolTree {
  // TODO: this is very similar to code in `NamespaceIdentifiers`, could maybe be merged...
  type Sub = Map[smt.Symbol, smt.Symbol]
  private def apply(e: ArgumentEq, subs: Sub): ArgumentEq =
    e.copy(range = apply(e.range, subs), argRange = apply(e.argRange, subs))
  private def apply(r: Range, subs: Sub): Range =
    if(subs.contains(r.sym)) r.copy(sym = subs(r.sym)) else r
  private def apply(node: InputNode, subs: Sub): InputNode =
    InputNode(node.next.map(apply(_, subs)), node.methods,
      node.constraints.map(substituteSmtSymbols(_, subs)), node.mappings.map(apply(_, subs)))
  private def apply(node: OutputNode, subs: Sub): OutputNode =
    OutputNode(node.next.map(apply(_, subs)), node.methods,
      node.constraints.map(substituteSmtSymbols(_, subs)), node.mappings.map(apply(_, subs)))
  def apply(node: StepNode, subs: Sub): StepNode =
    StepNode(node.next.map(apply(_, subs)), node.methods, node.id, node.isFork)
}

object NewVerificationAutomatonEncoder extends SMTHelpers {

  private def uniquePairs[N](s: Iterable[N]): Iterable[(N,N)] =
    for { (x, ix) <- s.zipWithIndex ; (y, iy) <- s.zipWithIndex ;  if ix < iy } yield (x, y)

  private def checkMethodsAreMutuallyExclusive(spec: Spec): Unit = {
    val guards = spec.untimed.methods.mapValues(_.guard)
    spec.protocols.values.foreach(p => assert(p.next.length == 1))
    val inputConstraints = spec.protocols.mapValues(_.next.head.constraintExpr)
    uniquePairs(spec.protocols.keys).foreach { case (a, b) =>
      val aConst = and(guards(a), inputConstraints(a))
      val bConst = and(guards(b), inputConstraints(b))
      val mutuallyExlusive = Checker.isUnsat(and(aConst, bConst))
      assert(mutuallyExlusive, s"We currently require all methods to have distinguishing inputs on the first cycle. This is not true for $a and $b!")
    }
  }

  private def findSteps(node: StepNode): Seq[StepNode] =
    Seq(node) ++ node.next.flatMap(_.next.flatMap(_.next.flatMap(findSteps)))

  private case class EncodeState(locToStep: Map[InstanceLoc, StepNode],
                                 guards: Map[String, smt.Expr],
                                 methodFuns: Map[smt.Symbol, smt.FunctionApplication],
                                 modelState: Seq[smt.Symbol])
  private def encodeState(st: PasoFsmState, next: Seq[PasoFsmEdge], info: EncodeState): PasoState = {
    val (ir, environmentAssumptions) = if(st.isFork) {

      // TODO: what do we do if non of the guards are true and we are stuck?
      val inputGuards = st.choices.map { loc =>
        val const = info.locToStep(loc).next.head.constraintExpr
        val guard = info.guards(loc.loc.proto)
        and(guard, const)
      }

      // other transactions that are currently executing, and will continue executing in parallel with the new transactions
      val activeInputs = st.active.map(info.locToStep(_).next.head)
      val activeInputInstances = st.active.map(_.instance)

      // TODO: check that the environment assumptions of all inputs are compatible
      val environmentAssumptions = conjunction(activeInputs.map(_.constraintExpr) ++ Seq(disjunction(inputGuards)))

      // the environment needs to follow the constraints of the active transaction
      // TODO: check that all inputs map different bits!
      val activeMappings = activeInputs.flatMap(_.mappings.map(ArgMap(tru, _)))

      val ii = st.choices.zip(inputGuards).map { case (loc, inGuard) =>
        val step = info.locToStep(loc)
        val inputNext = next.filter(_.active.contains(loc))
        val instance = loc.instance

        assert(step.next.length == 1)
        val input = step.next.head
        val inputMap = input.mappings.map(ArgMap(inGuard, _))

        encodeInputStep(Seq(instance) ++ activeInputInstances, inGuard, Seq(input) ++ activeInputs, inputMap ++ activeMappings, inputNext, info)
      }

      (ii, environmentAssumptions)
    } else {
      val activeInputs = st.active.map(info.locToStep(_).next.head)
      val activeInputInstances = st.active.map(_.instance)
      val inputNext = next // no need to filter since this is not a fork => all active inputs are active on all branches

      // TODO: check that the environment assumptions of all inputs are compatible
      val environmentAssumptions = conjunction(activeInputs.map(_.constraintExpr))

      // the environment needs to follow the constraints of the active transaction
      // TODO: check that all inputs map different bits!
      val activeMappings = activeInputs.flatMap(_.mappings.map(ArgMap(tru, _)))

      (Seq(encodeInputStep(activeInputInstances, tru, activeInputs, activeMappings, inputNext, info)), environmentAssumptions)
    }

    val inputMappings = ir.flatMap(_._1)
    val systemAssertions = ir.flatMap(_._2)
    val nextState = ir.flatMap(_._3)
    val stateUpdates = ir.flatMap(_._4)

    PasoState(st.id, inputMappings, environmentAssumptions, nextState, systemAssertions, stateUpdates)
  }

  private def encodeInputStep(instance: Int, inGuard: smt.Expr, input: InputNode, next: Seq[PasoFsmEdge], info: EncodeState): (Seq[ArgMap], Seq[OutputConstraint], Seq[NextState], Seq[StateUpdate]) = {
    // the environment needs to follow the constraints of the active transaction
    val mappings = input.mappings.map(ArgMap(inGuard, _))

    // there could be more than one OutputNode b/c of a branch in the protocol
    assert(input.next.length == next.length)
    val isBranch = input.next.length > 1

    // at least one of the following output constraints has to be true
    val systemAssertion = disjunction(input.next.map(_.constraintExpr))

    val oo = input.next.zip(next).map { case (output, nextEdge) =>
      val outGuard = if(isBranch) and(inGuard, output.constraintExpr) else inGuard
      val (const, update) = encodeOutputStep(instance, outGuard, mappings, output, info)
      val nextState = NextState(outGuard, nextEdge.to.id)
      (nextState, const, update)
    }

    val nextStates = oo.map(_._1)
    val constraints = Seq(OutputConstraint(inGuard, systemAssertion)) ++ oo.flatMap(_._2)
    val stateUpdates = oo.flatMap(_._3)
    (mappings, constraints, nextStates, stateUpdates)
  }

  private def encodeOutputStep(instance: Int, outGuard: smt.Expr, inputMap: Seq[ArgMap], node: OutputNode,
                               info: EncodeState): (Seq[OutputConstraint], Seq[StateUpdate]) = {
    assert(!node.isBranchPoint, "Cannot branch on steps! No way to distinguish between steps.")
    assert(!node.isFinal, "An output step cannot be final!")

    val mappings = node.mappings.map { m =>
      // substitute argument to refer to the correct mapping
      val argValue = callWithLatestArgumentValue(info.methodFuns(m.argRange.sym), inputMap)
      val guard = smt.Symbol(m.argRange.sym.id + ".valid", smt.BoolType)
      val guardValue = callWithLatestArgumentValue(info.methodFuns(guard), inputMap)
      // build constraint expressions
      val argExpr = if(m.argRange.isFullRange) argValue else app(smt.BVExtractOp(hi=m.argRange.hi, lo=m.argRange.lo), argValue)
      val equality = eq(m.range.toExpr(), argExpr)
      OutputConstraint(outGuard, implies(guardValue, equality))
    }

    // if this is a fork node --> commit any updates to the architectural state
    val updates = if(node.next.head.isFork) {
      assert(node.methods.size == 1, "Cannot have overlapping methods at the commit point!")
      val meth = node.methods.head

      // find all state updates for this method
      info.modelState.map { state =>
        val suffix = if(instance == 0) "." + meth else "." + meth + "$" + instance
        val stateUpdate = state.copy(id = state.id + suffix)
        val updateValue = callWithLatestArgumentValue(info.methodFuns(stateUpdate), inputMap)
        StateUpdate(outGuard, state, updateValue)
      }
    } else { Seq() }

    (mappings, updates)
  }

  private def callWithLatestArgumentValue(foo: smt.FunctionApplication, map: Seq[ArgMap]): smt.FunctionApplication = {
    val args = foo.args.map(a => getLatestArgumentValue(a.asInstanceOf[smt.Symbol], map))
    foo.copy(args = args)
  }

  /** Returns the argument state if the argument is not mapped in the current cycle. */
  private def getLatestArgumentValue(arg: smt.Symbol, map: Seq[ArgMap]): smt.Expr = {
    // TODO: for now we only support a single full update --> need to implement partial updates at some point
    assert(map.forall(_.eq.argRange.isFullRange))
    map.find(_.eq.argRange.sym == arg).map(_.eq.range.toExpr()).getOrElse(arg)
  }

  private def createProtocolInstance(name: String, instance: Int, node: StepNode, method: MethodSemantics): Iterable[(InstanceLoc, StepNode)] = {
    require(instance >= 0)
    if(instance == 0) {
      findSteps(node).map(s => InstanceLoc(0, Loc(name, s)) -> s)
    } else {
      // rename non default instance
      val args = method.inputs ++ method.outputs.flatMap(o => Seq(o.sym, o.guardSym))
      val subs: Map[smt.Symbol, smt.Symbol] = args.map(a => a -> a.copy(id = a.id + "$" + instance)).toMap
      val subNode = DuplicateProtocolTree(node, subs)
      findSteps(subNode).map(s => InstanceLoc(instance, Loc(name, s)) -> s)
    }
  }

  private def createFunctionAppSubs(name: String, instance: Int, method: MethodSemantics): Iterable[(smt.Symbol, smt.FunctionApplication)] = {
    require(instance >= 0)
    val rename: String => String = if(instance == 0) { id: String => id } else { id: String => id + "$" + instance }
    def r(s: smt.Symbol): smt.Symbol = s.copy(id = rename(s.id))

    // this is similar to UntimedModel.functionAppSubs, but renames the output symbols
    val apps = method.outputs.flatMap(o => Seq(r(o.sym) -> o.functionApp, r(o.guardSym) -> o.guardFunctionApp)) ++
      // for state updated we need to add the s".$name" suffix to avoid name conflicts
      method.updates.map(u => u.copy(sym = u.sym.copy(id = u.sym.id + s".$name"))).map(u => r(u.sym) -> u.functionApp)

    // replace the arguments to the function applications
    val argSubs = method.inputs.map(a => a -> r(a)).toMap
    apps.map{ case (sym, app) => (sym, app.copy(args = app.args.map(_.asInstanceOf[smt.Symbol]).map(a => argSubs.getOrElse(a, a)))) }
  }

  def run(spec: Spec, prefix: String, resetAssumption: smt.Expr = tru, switchAssumesAndGuarantees: Boolean = false): smt.TransitionSystem = {
    // we check that all methods are mutually exclusive
    checkMethodsAreMutuallyExclusive(spec)

    // we create the basic fsm that helps us keep track of the system
    val fsm = PasoFsmEncoder(spec.protocols).run()

    // make copies of protocols where necessary to create unique protocol trees and function applications
    val locToStep = spec.protocols.flatMap{ case (name, step) =>
      (0 until fsm.instances(name)).flatMap(inst => createProtocolInstance(name, inst, step, spec.untimed.methods(name)))
    }.toMap
    val methodFuns = spec.untimed.methods.flatMap { case(name, meth) =>
      (0 until fsm.instances(name)).flatMap(inst => createFunctionAppSubs(name, inst, meth))
    }.toMap


    // encode states
    val edgesByFromId = fsm.edges.groupBy(_.from.id)
    val guards = spec.untimed.methods.mapValues(_.guard)
    val info = EncodeState(locToStep, guards, methodFuns, spec.untimed.state.map(_.sym))
    val states = fsm.states.map(s => encodeState(s, edgesByFromId(s.id), info))

    // turn states into state transition system
    assert(states.head.id == 0, "Expected first state to be the start state!")
    PasoCombinedAutomatonEncoder.run(prefix, resetAssumption, states.head, states, switchAssumesAndGuarantees)
  }
}

/** Much Simpler Version of PasoFsmEncoder + NewVerificationAutomatonEncoder but Cannot Deal with Fork/Pipelining :( */
case class OldVerificationAutomatonEncoder(methodFuns: Map[smt.Symbol, smt.FunctionApplication], modelState: Seq[smt.Symbol], switchAssumesAndGuarantees: Boolean = false) extends SMTHelpers {

  def run(proto: StepNode, prefix: String, resetAssumption: smt.Expr): smt.TransitionSystem = {
    val start_id = visit(proto)
    val start = states.find(_.id == start_id).get
    PasoCombinedAutomatonEncoder.run(prefix, resetAssumption, start, states, switchAssumesAndGuarantees)
  }

  private val StartId: Int = 0
  private var stateCounter: Int = StartId
  private val states = mutable.ArrayBuffer[PasoState]()
  private def getStateId: Int = { val ii = stateCounter; stateCounter += 1; ii}

  private def visit(node: StepNode): Int = {
    if(node.isFinal) { return StartId }

    val id = getStateId

    // either of the following input constraints could be true
    val environmentAssumptions = disjunction(node.next.map(_.constraintExpr))

    // TODO: in case there is an input branch, identifying the disagreeing constraint that separates
    //       the branches would lead to a smaller formula,
    //       i.e. a -> x and b -> y instead of (a and c) -> x and (b and c) -> y
    val inputGuards = if(node.isBranchPoint) { node.next.map(_.constraintExpr) } else { Seq(tru) }

    val ir = node.next.zip(inputGuards).map { case (input, inGuard) => visit(inGuard, input) }
    val inputMappings = ir.flatMap(_._1)
    val systemAssertions = ir.flatMap(_._2)
    val nextState = ir.flatMap(_._3)
    val stateUpdates = ir.flatMap(_._4)

    val s = PasoState(id, inputMappings, environmentAssumptions, nextState, systemAssertions, stateUpdates)
    states.append(s)
    s.id
  }

  def visit(inGuard: smt.Expr, node: InputNode): (Seq[ArgMap], Seq[OutputConstraint], Seq[NextState], Seq[StateUpdate]) = {
    val mappings = node.mappings.map(ArgMap(inGuard, _))

    // at least one of the following output constraints has to be true
    val systemAssertion = disjunction(node.next.map(_.constraintExpr))

    // TODO: in case there is an input branch, identifying the disagreeing constraint that separates
    //       the branches would lead to a smaller formula,
    //       i.e. a -> x and b -> y instead of (a and c) -> x and (b and c) -> y
    // note that return argument maps cannot be used to distinguish the path
    val outputGuards = if(node.isBranchPoint) { node.next.map(o => and(inGuard, o.constraintExpr)) } else { Seq(inGuard) }
    val nextStatesAndMappingsAndUpdates = node.next.zip(outputGuards).map{
      case(output, outGuard) => visit(outGuard, mappings, output)
    }

    val constraints = Seq(OutputConstraint(inGuard, systemAssertion)) ++ nextStatesAndMappingsAndUpdates.flatMap(_._2)
    val nextStates = nextStatesAndMappingsAndUpdates.map(_._1)
    val stateUpdates = nextStatesAndMappingsAndUpdates.flatMap(_._3)
    (mappings, constraints, nextStates, stateUpdates)
  }

  def visit(outGuard: smt.Expr, inputMap: Seq[ArgMap], node: OutputNode): (NextState, Seq[OutputConstraint], Seq[StateUpdate]) = {
    assert(!node.isBranchPoint, "Cannot branch on steps! No way to distinguish between steps.")
    assert(!node.isFinal, "TODO: deal with final output nodes")

    val mappings = node.mappings.map { m =>
      // substitute argument to refer to the correct mapping
      val argValue = callWithLatestArgumentValue(methodFuns(m.argRange.sym), inputMap)
      val guard = smt.Symbol(m.argRange.sym.id + ".valid", smt.BoolType)
      val guardValue = callWithLatestArgumentValue(methodFuns(guard), inputMap)
      // build constraint expressions
      val argExpr = if(m.argRange.isFullRange) argValue else app(smt.BVExtractOp(hi=m.argRange.hi, lo=m.argRange.lo), argValue)
      val equality = eq(m.range.toExpr(), argExpr)
      OutputConstraint(outGuard, implies(guardValue, equality))
    }

    val next = NextState(outGuard, visit(node.next.head))

    // if this is the last node before going back into the idle state --> commit any updates to the architectural state
    val updates = if(node.next.head.isFinal) {
      assert(node.methods.size == 1, "Cannot have overlapping methods at the commit point!")
      val meth = node.methods.head

      // find all state updates for this method
      modelState.map { state =>
        val stateUpdate = state.copy(id = state.id + s".$meth")
        val updateValue = callWithLatestArgumentValue(methodFuns(stateUpdate), inputMap)
        StateUpdate(outGuard, state, updateValue)
      }
    } else { Seq() }

    (next, mappings, updates)
  }

  private def callWithLatestArgumentValue(foo: smt.FunctionApplication, map: Seq[ArgMap]): smt.FunctionApplication = {
    val args = foo.args.map(a => getLatestArgumentValue(a.asInstanceOf[smt.Symbol], map))
    foo.copy(args = args)
  }

  /** Returns the argument state if the argument is not mapped in the current cycle. */
  private def getLatestArgumentValue(arg: smt.Symbol, map: Seq[ArgMap]): smt.Expr = {
    // TODO: for now we only support a single full update --> need to implement partial updates at some point
    assert(map.forall(_.eq.argRange.isFullRange))
    map.find(_.eq.argRange.sym == arg).map(_.eq.range.toExpr()).getOrElse(arg)
  }
}

object Checker extends SMTHelpers with HasSolver {
  val solver = new YicesInterface
  def isSat(e: smt.Expr): Boolean = check(e).isTrue
  def isUnsat(e: smt.Expr): Boolean = check(e).isFalse
  def isValid(e: smt.Expr): Boolean = isUnsat(app(smt.NegationOp, e))
}

trait HasSolver {
  val solver: Solver
  def check(e: smt.Expr): smt.SolverResult = solver.check(e)
}

object VerificationGraphToDot extends SMTHelpers {
  type Arrows = Seq[(VerificationNode, VerificationNode, String)]

//  private def visit(node: PendingInputNode): Arrows = node.next.flatMap(visit(_, node))
//  private def visit(node: PendingOutputNode): Arrows = node.next.flatMap(visit(_, node))
//  private def mkMsg(constraints: Seq[smt.Expr], mappings: Seq[smt.Expr]): String = {
//    (constraints ++ mappings).map(SMTSimplifier.simplify).mkString(", ")
//  }
//  private def visit(edge: InputEdge, parent: VerificationNode): Arrows = {
//    val msg = mkMsg(edge.constraints, edge.mappings)
//    Seq((parent, edge.next, msg)) ++ visit(edge.next)
//  }
//  private def visit(edge: OutputEdge, parent: VerificationNode): Arrows = {
//    val msg = mkMsg(edge.constraints, edge.mappings)
//    Seq((parent, edge.next, msg)) ++ visit(edge.next)
//  }

  def apply(name: String, graph: StepNode): String = ???
//  {
//    val arrows = visit(graph)
//    val edges = arrows.flatMap(a => Set(a._1, a._2)).toSet
//    val edgeToId = edges.zipWithIndex.toMap
//    val edgeIds = edgeToId.values
//
//    val nodes = edgeIds.map(i => s"$i [shape=point]").mkString("\n")
//    val connections = arrows.map(a => s"""${edgeToId(a._1)} -> ${edgeToId(a._2)} [label="${a._3}"]""").mkString("\n")
//
//    s"""
//      |digraph $name {
//      |  rankdir="LR";
//      |  $nodes
//      |  $connections
//      |}
//      |""".stripMargin
//  }
}

object ShowDot {
  def apply(src: String, fileName: String = "test.dot"): Unit = {
    val ff = new FileWriter(fileName)
    ff.write(src)
    ff.close()
    s"xdot $fileName"!!
  }
}