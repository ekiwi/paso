// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.passes.PassException
import paso.verification.UntimedModel
import maltese.smt
import maltese.smt.solvers.Yices2

import scala.collection.mutable

/**
 * Combines the untimed module and all its protocols into a "Paso Automaton" transition system.
 *
 * */
class PasoAutomatonEncoder(untimed: UntimedModel, protocols: Iterable[ProtocolGraph]) {
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

  /** exclusively tracks the control flow state, called an edge to avoid confusion with transitions */
  case class StateEdge(from: Int, to: Int, guard: Seq[smt.BVExpr])
  /** collects all state transitions */
  private val stateEdges = mutable.ArrayBuffer[StateEdge]()

  case class StateGuarded(stateId: Int, pred: Guarded)
  /** collects all assumptions over the inputs, depending on the state */
  private val assumptions = mutable.ArrayBuffer[StateGuarded]()

  /** collects all assertions depending on the state */
  private val assertions = mutable.ArrayBuffer[StateGuarded]()

  case class StateGuardedMapping(stateId: Int, map: GuardedMapping)
  /** collects all argument mappings for all protocols depending on the state */
  private val mappings = mutable.ArrayBuffer[StateGuardedMapping]()

  case class GuardedCommit(stateId: Int, guard: smt.BVExpr, commit: smt.BVSymbol)
  /** collects all state updates for all protocols depending on the state */
  private val commits = mutable.ArrayBuffer[GuardedCommit]()

  /** symbols that describe which protocol is starting to execute this cycle,
   *  this relies on these conditions to be mutually exclusive
   */
  private val newTransaction = protocols.map{ p => p.name -> smt.BVSymbol(p.name + ".active", 1) }.toMap

  def run(): smt.TransitionSystem = {
    // check that all transactions are mutually exclusive in their first transition
    val guards = untimed.methods.map(m => untimed.name + "." + m.name -> smt.BVSymbol(m.ioName + "_guard", 1)).toMap // TODO: extract complete guard expression over states from transition system
    val newTransactionPred = protocols
      .map{ p => p.transitions.head.assumptions.map(_.toExpr) :+ guards(p.name) }.map(smt.BVAnd(_)).toSeq
    ensureMutuallyExclusive(newTransactionPred, protocols.map(_.info))

    // we start in a state where no protocols are running
    val start = getStateId(active = List(), start = true)
    // recursively encode states until we reach a fixed point
    while(statesToBeEncoded.nonEmpty) {
      encodeState(statesToBeEncoded.pop())
    }


    // TODO: return a case class with all parts of our encoding
    println()
    ???
  }

  private def encodeState(st: State): Unit = {
    // we can add all assertions, assumptions and mappings from active transitions as they are already properly guarded
    // (the only thing missing is the state which we now add)
    st.active.map(transition).foreach(addTransition(st.id, None, _))

    if(!st.start) {
      // find all possible combinations of (non-final) next locations for the active protocols
      val nextActive = product(st.active.map(getNonFinalNext))
      // if we do not start any new transactions, we just encode the nextActive states
      nextActive.foreach { na =>
        val next = na.map(_._1)
        val nextId = getStateId(active = na.map(_._2), start = next.exists(_.fork))
        // TODO: we also need to encode final transitions!
        stateEdges += StateEdge(from=st.id, to=nextId, guard = next.map(_.guard))
      }
    } else {
      // if we do need to start new transactions, we need to chose an unused copy of each transaction's protocol
      val guardedNewLocs = protocols.map { p =>
        newTransaction(p.name) -> getFreeCopy(p.name, st.active)
      }

      // We need to assume that one of the guards is true.
      // Since they are all mutually exclusive (checked earlier) if at least one is true, exactly one is true.
      val pickOne = smt.BVOr(guardedNewLocs.map(_._1))
      assumptions += StateGuarded(st.id, Guarded(smt.True(), pickOne))

      // we add all inputs, assumptions, mappings, assertions and commits, but guarded by whether we actually start the transaction
      guardedNewLocs.foreach { case (guard, loc) => addTransition(st.id, Some(guard), transition(loc)) }

      // now we need to combine all normal next locs with each one of the possibly started locations
      guardedNewLocs.foreach { case (newGuard, newLoc) =>
        // find all possible combinations of (non-final) next locations for the active protocols + one new protocol
        val nextActive = product((st.active :+ newLoc).map(getNonFinalNext))
        nextActive.foreach { na =>
          val next = na.map(_._1)
          val nextId = getStateId(active = na.map(_._2), start = next.exists(_.fork))
          // we only take this next step if we actually chose this new transaction (which is why we add the newGuard)
          stateEdges += StateEdge(from=st.id, to=nextId, guard = next.map(_.guard) :+ newGuard)
        }
      }
    }
  }

  /** add all assumptions, assertions, mappings and commit to the global data structure */
  private def addTransition(stateId: Int, guard: Option[smt.BVExpr], tran: Transition): Unit = {
    def addGuard(e: smt.BVExpr): smt.BVExpr = guard.map(smt.BVAnd(_, e)).getOrElse(e)
    assumptions ++= tran.assumptions.map(g => StateGuarded(stateId, g.copy(guard = addGuard(g.guard))))
    mappings ++= tran.mappings.map(g => StateGuardedMapping(stateId, g.copy(guard = addGuard(g.guard))))
    assertions ++= tran.assertions.map(g => StateGuarded(stateId, g.copy(guard = addGuard(g.guard))))
    commits ++= tran.next.collect{ case Next(g, _, Some(commit), _, _) => GuardedCommit(stateId, addGuard(g), commit) }
  }

  private def getFreeCopy(name: String, active: Iterable[Loc]): Loc = {
    val activeIds = active.filter(_.name == name).map(_.copyId).toSet
    val copyId = Iterator.from(0).find(ii => !activeIds.contains(ii)).get
    Loc(name, 0, copyId)
  }

  private def getNonFinalNext(loc: Loc): Seq[(Next, Loc)] =
    transition(loc).next.filterNot(_.isFinal).map(n => (n, loc.copy(transition = n.cycleId)))

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

  private val solver = Yices2()
  private def isSat(cond: smt.BVExpr): Boolean = solver.check(cond, produceModel = false).isSat
  private def isUnSat(cond: smt.BVExpr): Boolean = solver.check(cond, produceModel = false).isUnSat
}