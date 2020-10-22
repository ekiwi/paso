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
  private val inputAssumptions = mutable.ArrayBuffer[StateGuarded]()

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
  private val newTransaction = protocols.map{ p => p.name -> smt.BVSymbol(p.name + ".active", 1) }

  def run(): smt.TransitionSystem = {
    // check that all transactions are mutually exclusive in their first transition
    val guards = untimed.methods.map(m => m.name -> smt.BVSymbol(m.ioName + "_guard", 1)).toMap // TODO: extract complete guard expression over states from transition system
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
    ???
  }

  private def encodeState(st: State): Unit = {
    // we can add all assertions, assumptions and mappings from active transitions as they are already properly guarded
    // (the only thing missing is the state which we now add)
    val active = st.active.map(transition)
    inputAssumptions ++= active.flatMap(_.assumptions).map(StateGuarded(st.id, _))
    mappings ++= active.flatMap(_.mappings).map(StateGuardedMapping(st.id, _))
    assertions ++= active.flatMap(_.assertions).map(StateGuarded(st.id, _))
    commits ++= active.flatMap(_.next).collect{ case Next(guard, _, Some(commit), _, _) => GuardedCommit(st.id, guard, commit) }

    // find all possible combinations of (non-final) next locations for the active protocols
    val nextActive = product(st.active.map(getNonFinalNext))

    if(!st.start) {
      // if we do not start any new transactions, we just encode the nextActive states
      nextActive.foreach { na =>
        val next = na.map(_._1)
        val nextId = getStateId(active = na.map(_._2), start = next.exists(_.fork))
        stateEdges += StateEdge(from=st.id, to=nextId, guard = next.map(_.guard))
      }
    } else {
      // if we do need to start new transactions, we need to chose an unused copy of each transaction's protocol


    }





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