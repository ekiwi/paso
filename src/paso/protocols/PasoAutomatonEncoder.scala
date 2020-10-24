// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import paso.verification.UntimedModel
import maltese.smt
import maltese.smt.solvers.Solver

import scala.collection.mutable

case class PasoAutomaton(
  states: Array[PasoState], edges: Seq[PasoStateEdge], assumptions: Seq[PasoStateGuarded],
  assertions: Seq[PasoStateGuarded], mappings: Seq[PasoStateGuardedMapping],
  commits: Seq[PasoGuardedCommit], transactionStartSignals: Seq[(String, smt.BVExpr)],
  untimed: UntimedModel
)
case class PasoState(id: Int, isStart: Boolean, info: String)
/** exclusively tracks the control flow state, called an edge to avoid confusion with transitions */
case class PasoStateEdge(from: Int, to: Int, guard: List[smt.BVExpr])
case class PasoStateGuarded(stateId: Int, pred: Guarded)
case class PasoStateGuardedMapping(stateId: Int, map: GuardedMapping)
case class PasoGuardedCommit(stateId: Int, guard: List[smt.BVExpr], commit: smt.BVSymbol)

/**
 * Combines the untimed module and all its protocols into a "Paso Automaton" transition system.
 *
 * */
class PasoAutomatonEncoder(untimed: UntimedModel, protocols: Iterable[ProtocolGraph], solver: Solver) {
  /** Identifies a transition in a particular protocol as well as the copyId of the protocol in case it needed to be duplicated */
  private case class Loc(name: String, transition: Int, copyId: Int = 0) {
    override def toString: String = s"$name$$$copyId@$transition"
  }
  private val transitionMap: Map[String, Transition] =
    protocols.flatMap { p => p.transitions.zipWithIndex.map { case (t, i) => s"${p.name}$$0@$i" -> t }}.toMap
  private def transition(loc: Loc): Transition = {
    assert(loc.copyId == 0, "TODO: lazily copy transitions as copies occur!")
    transitionMap(loc.toString)
  }

  /** States are characterized by the active protocols and whether a new protocol is going to be started. */
  private case class State(id: Int, active: Seq[Loc], start: Boolean) {
    def toIndex: String = "{" + active.map(_.toString).sorted.mkString(", ") + "}" + (if(start) " (F)" else "")
  }
  /** States are accumulated as we explore the possible execution of the combined protocols. */
  private val states = mutable.HashMap[String, State]()
  private var stateCount = 0
  private def getNewStateId: Int = { val i = stateCount; stateCount += 1; i }
  private def getStateId(active: Seq[Loc], start: Boolean): Int = {
    val index = State(0, active, start).toIndex
    val id = states.get(index).map(_.id).getOrElse(-1)
    if(id >= 0) { return id }
    // create new state and add it to the to be encoded stack
    val state = State(getNewStateId, active, start)
    states(index) = state
    statesToBeEncoded.push(state)
    state.id
  }
  private val statesToBeEncoded = mutable.ArrayStack[State]()

  /** collects all state transitions */
  private val stateEdges = mutable.ArrayBuffer[PasoStateEdge]()

  /** collects all assumptions over the inputs, depending on the state */
  private val assumptions = mutable.ArrayBuffer[PasoStateGuarded]()

  /** collects all assertions depending on the state */
  private val assertions = mutable.ArrayBuffer[PasoStateGuarded]()

  /** collects all argument mappings for all protocols depending on the state */
  private val mappings = mutable.ArrayBuffer[PasoStateGuardedMapping]()

  /** collects all state updates for all protocols depending on the state */
  private val commits = mutable.ArrayBuffer[PasoGuardedCommit]()

  /** symbols that describe which protocol is starting to execute this cycle,
   *  this relies on these conditions to be mutually exclusive
   */
  private val newTransaction = protocols.map{ p => p.name -> smt.BVSymbol(p.info.methodPrefix + "active", 1) }.toMap

  def run(): PasoAutomaton = {
    // check that all transactions are mutually exclusive in their first transition
    val guards = untimed.methods.map(m => untimed.name + "." + m.name -> smt.BVSymbol(m.fullIoName + "_guard", 1)).toMap // TODO: extract complete guard expression over states from transition system
    val newTransactionPred = protocols
      .map{ p => p.transitions.head.assumptions.map(_.toExpr) :+ guards(p.name) }.map(smt.BVAnd(_)).toSeq
    ensureMutuallyExclusive(newTransactionPred, protocols.map(_.info))

    // we start in a state where no protocols are running
    val startId = getStateId(active = List(), start = true)
    assert(startId == 0)
    // recursively encode states until we reach a fixed point
    while(statesToBeEncoded.nonEmpty) {
      encodeState(statesToBeEncoded.pop())
    }

    PasoAutomaton(states.values.toArray.map(s => PasoState(s.id, s.start, s.toString)).sortBy(_.id), stateEdges.toSeq,
      assumptions.toSeq, assertions.toSeq, mappings.toSeq, commits.toSeq,
      newTransactionPred.zip(protocols).map{ case (expr, p) => newTransaction(p.name).name -> expr },
      untimed)
  }

  private def encodeState(st: State): Unit = {
    // we can add all assertions, assumptions and mappings from active transitions as they are already properly guarded
    // (the only thing missing is the state which we now add)
    st.active.map(transition).foreach(addTransition(st.id, List(), _))

    if(!st.start) {
      // find all possible combinations of next locations for the active protocols
      val nextActive = product(st.active.map(getNext))
      // if we do not start any new transactions, we just encode the nextActive states
      nextActive.foreach { na =>
        val next = na.map(_._1)
        val active = na.map(_._2).filterNot(_.transition == 0) // filter out starting states
        val nextId = getStateId(active = active, start = next.exists(_.fork))
        stateEdges += PasoStateEdge(from=st.id, to=nextId, guard = next.flatMap(_.guard).toList)
      }
    } else {
      // if we do need to start new transactions, we need to chose an unused copy of each transaction's protocol
      val guardedNewLocs = protocols.map { p =>
        newTransaction(p.name) -> getFreeCopy(p.name, st.active)
      }

      // We need to assume that one of the guards is true.
      // Since they are all mutually exclusive (checked earlier) if at least one is true, exactly one is true.
      val pickOne = smt.BVOr(guardedNewLocs.map(_._1))
      assumptions += PasoStateGuarded(st.id, Guarded(List(), pickOne))

      // we add all inputs, assumptions, mappings, assertions and commits, but guarded by whether we actually start the transaction
      guardedNewLocs.foreach { case (guard, loc) => addTransition(st.id, List(guard), transition(loc)) }

      // now we need to combine all normal next locs with each one of the possibly started locations
      guardedNewLocs.foreach { case (newGuard, newLoc) =>
        // find all possible combinations of next locations for the active protocols + one new protocol
        val nextActive = product((st.active :+ newLoc).map(getNext))
        nextActive.foreach { na =>
          val next = na.map(_._1)
          val active = na.map(_._2).filterNot(_.transition == 0) // filter out starting states
          val nextId = getStateId(active = active, start = next.exists(_.fork))
          // we only take this next step if we actually chose this new transaction (which is why we add the newGuard)
          stateEdges += PasoStateEdge(from=st.id, to=nextId, guard = (next.flatMap(_.guard) :+ newGuard).toList)
        }
      }
    }
  }

  /** add all assumptions, assertions, mappings and commit to the global data structure */
  private def addTransition(stateId: Int, guard: List[smt.BVExpr], tran: Transition): Unit = {
    def addGuard(e: List[smt.BVExpr]): List[smt.BVExpr] = e ++ guard
    assumptions ++= tran.assumptions.map(g => PasoStateGuarded(stateId, g.copy(guard = addGuard(g.guard))))
    mappings ++= tran.mappings.map(g => PasoStateGuardedMapping(stateId, g.copy(guard = addGuard(g.guard))))
    assertions ++= tran.assertions.map(g => PasoStateGuarded(stateId, g.copy(guard = addGuard(g.guard))))
    commits ++= tran.next.collect{ case Next(g, _, Some(commit), _, _) => PasoGuardedCommit(stateId, addGuard(g), commit) }
  }

  private def getFreeCopy(name: String, active: Iterable[Loc]): Loc = {
    val activeIds = active.filter(_.name == name).map(_.copyId).toSet
    val copyId = Iterator.from(0).find(ii => !activeIds.contains(ii)).get
    Loc(name, 0, copyId)
  }

  /** returns all transitions */
  private def getNext(loc: Loc): Seq[(Next, Loc)] = {
    // for now, let's not try to merge as it may not be needed
    //val sameBody = transition(loc).next.groupBy(n => (n.cycleId, n.fork))
    // merge all next that have the same next property and fork
    //val merged = sameBody.map{ case (_, ns) => ns.head.copy(guard = smt.BVOr(ns.map(_.guard))) }
    transition(loc).next.map(n => (n, loc.copy(transition = n.cycleId)))
  }

  private def ensureMutuallyExclusive(pred: Seq[smt.BVExpr], info: Iterable[ProtocolInfo]): Unit = {
    pred.zipWithIndex.foreach { case (predI, i) =>
      pred.zipWithIndex.drop(i + 1).foreach { case (predJ, j) =>
        val exclusive = isUnSat(smt.BVAnd(predI, predJ))
        if(!exclusive) {
          val (iName, jName) = (info.drop(i).head.name, info.drop(j).head.name)
          val msg = s"The protocols for $iName and $jName are not mutually exclusive in the first cycle.\n" +
          "This is currently not supported."
          throw new RuntimeException(msg)
        }
      }
    }
  }

  // https://stackoverflow.com/questions/8321906/lazy-cartesian-product-of-several-seqs-in-scala/8569263
  private def product[N](xs: Seq[Seq[N]]): Seq[Seq[N]] =
    xs.foldLeft(Seq(Seq.empty[N])){ (x, y) => for (a <- x.view; b <- y) yield a :+ b }

  private def isUnSat(cond: smt.BVExpr): Boolean = solver.check(cond, produceModel = false).isUnSat
}