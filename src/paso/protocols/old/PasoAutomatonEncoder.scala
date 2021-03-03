// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols.old

import maltese.smt
import maltese.smt.solvers.Solver
import paso.formal.UntimedModel
import paso.protocols.old

import scala.collection.mutable

case class PasoAutomaton(
  states: Array[PasoState], edges: Seq[PasoStateEdge], assumptions: Seq[PasoStateGuarded],
  assertions: Seq[PasoStateGuarded], mappings: Seq[PasoStateGuardedMapping],
  commits: Seq[PasoGuardedSignal], transactionActiveSignals: Seq[(String, smt.BVExpr)],
  longestPath: Int, untimed: UntimedModel, protocolCopies: Seq[(String, Int)]
)
case class PasoState(id: Int, isStart: Boolean, info: String)
/** exclusively tracks the control flow state, called an edge to avoid confusion with transitions */
case class PasoStateEdge(from: Int, to: Int, guard: List[smt.BVExpr], endTransaction: Seq[String], startTransaction: Option[String] = None)
case class PasoStateGuarded(stateId: Int, pred: Guarded)
case class PasoStateGuardedMapping(stateId: Int, map: GuardedMapping)
case class PasoGuardedSignal(stateId: Int, guard: List[smt.BVExpr], signal: smt.BVSymbol)

/**
 * Combines the untimed module and all its protocols into a "Paso Automaton" transition system.
 *
 * */
class PasoAutomatonEncoder(untimed: UntimedModel, protocols: Iterable[ProtocolGraph], solver: Solver) {
  /** Identifies a transition in a particular protocol as well as the copyId of the protocol in case it needed to be duplicated */
  private case class Loc(name: String, transition: Int, copyId: Int = 0) {
    override def toString: String = s"$name$$$copyId@$transition"
    def nameAndCopyId: String = s"$name$$$copyId"
  }
  private val transitionMap = mutable.HashMap[String, Transition]()
  private def transition(loc: Loc): Transition = {
    if(!transitionMap.contains(loc.toString)) {
      copyProtocol(loc)
    }
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
  private val commits = mutable.ArrayBuffer[PasoGuardedSignal]()

  /** symbols that describe which protocol is starting to execute this cycle,
   *  this relies on these conditions to be mutually exclusive
   */
  private val newTransaction = protocols.map{ p => p.name -> smt.BVSymbol(p.info.methodPrefix + "active", 1) }.toMap

  def run(): PasoAutomaton = {
    // check that all transactions are mutually exclusive in their first transition
    val guards = untimed.methods.map(m => untimed.name + "." + m.name -> smt.BVSymbol(m.fullIoName + "_guard", 1)).toMap
    // TODO: extract complete guard expression over states from transition system, to allow for transactions with mutually exclusive guards
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

    // printAutomaton()

    val longestPath = protocols.map(_.info.longestPath).max
    old.PasoAutomaton(states.values.toArray.map(s => PasoState(s.id, s.start, s.toString)).sortBy(_.id), stateEdges.toSeq,
      assumptions.toSeq, assertions.toSeq, mappings.toSeq, commits.toSeq,
      newTransactionPred.zip(protocols).map{ case (expr, p) => newTransaction(p.name).name -> expr },
      longestPath, untimed, protocolCopies.toSeq)
  }

  // for debugging
  private def printAutomaton(): Unit = {
    println(s"${untimed.sys.name} Paso Automaton:")
    states.values.toSeq.sortBy(_.id).foreach(println)
    stateEdges.foreach(println)
    println()
  }

  private def encodeState(st: State): Unit = {
    // we can add all assertions, assumptions and mappings from active transitions as they are already properly guarded
    // (the only thing missing is the state which we now add)
    st.active.map(transition).foreach(addTransition(st.id, List(), _))

    // TODO: check that ioAccess is compatible!

    if(!st.start) {
      // check that active transitions are compatible:
      if(st.active.length > 1) {
        Transition.checkCompatibility(isSat, st.active.map(transition))
      }

      // find all possible combinations of next locations for the active protocols
      val nextActive = product(st.active.map(getNext))

      // if we do not start any new transactions, we just encode the nextActive states
      nextActive.foreach { na =>
        val next = na.map(_._1)
        val active = na.map(_._2).filterNot(_.transition == 0) // filter out starting states
        val nextId = getStateId(active = active, start = next.exists(_.fork))
        // find any active transaction that is a final transaction
        val endTransactions = na.filter(_._1.isFinal).map(_._2.nameAndCopyId)
        stateEdges += PasoStateEdge(from=st.id, to=nextId, guard = next.flatMap(_.guard).toList, endTransactions.toSeq)
      }
    } else {
      // if we do need to start new transactions, we need to chose an unused copy of each transaction's protocol
      val guardedNewLocs = protocols.map { p =>
        // TODO: choose start signal depending on actual copy ... (or remove any symbols from the start signal)
        newTransaction(p.name) -> getFreeCopy(p.name, st.active)
      }

      // check that active transitions are compatible:
      if(st.active.nonEmpty) {
        val activeTransitions = st.active.map(transition)
        guardedNewLocs.map(_._2).map(transition).foreach { newTransition =>
          Transition.checkCompatibility(isSat, activeTransitions :+ newTransition)
        }
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
          // find any active transaction that is a final transaction
          val endTransactions = na.filter(_._1.isFinal).map(_._2.nameAndCopyId)
          // we only take this next step if we actually chose this new transaction (which is why we add the newGuard)
          stateEdges += PasoStateEdge(from=st.id, to=nextId, guard = (next.flatMap(_.guard) :+ newGuard).toList,
            endTransaction = endTransactions.toSeq, startTransaction = Some(newLoc.nameAndCopyId))
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
    commits ++= tran.next.collect{ case Next(g, _, Some(commit), _, _) => PasoGuardedSignal(stateId, addGuard(g), commit) }
  }

  private def getFreeCopy(name: String, active: Iterable[Loc]): Loc = {
    val activeIds = active.filter(_.name == name).map(_.copyId).toSet
    val copyId = Iterator.from(0).find(ii => !activeIds.contains(ii)).get
    Loc(name, 0, copyId)
  }

  /** returns all transitions */
  private def getNext(loc: Loc): Seq[(Next, Loc)] = {
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

  // adds a copy of all transitions in the protocol to transitionCopyMap
  private def copyProtocol(loc: Loc): Unit = {
    val original = protocols.find(_.name == loc.name).getOrElse(throw new RuntimeException(s"Unknown protocol: ${loc.name}"))
    assert(loc.copyId == protocolCopies(original.name))
    protocolCopies(original.name) = loc.copyId + 1
    val suffix = s"$$${loc.copyId}"
    transitionMap ++= ProtocolCopy(original, suffix)
  }
  private val protocolCopies = mutable.HashMap[String, Int]() ++ protocols.map(p => p.name -> 0)

  // https://stackoverflow.com/questions/8321906/lazy-cartesian-product-of-several-seqs-in-scala/8569263
  private def product[N](xs: Seq[Seq[N]]): Seq[Seq[N]] =
    xs.foldLeft(Seq(Seq.empty[N])){ (x, y) => for (a <- x.view; b <- y) yield a :+ b }

  private def isUnSat(cond: smt.BVExpr): Boolean = solver.check(cond, produceModel = false).isUnSat
  private def isSat(cond: smt.BVExpr): Boolean = solver.check(cond, produceModel = false).isSat
}

object ProtocolCopy {
  def apply(original: ProtocolGraph, suffix: String): Iterable[(String, Transition)] = {
    // replace arguments, previous argument, return values as well as the enabled commit signal
    val commitSignal = original.info.methodPrefix + "enabled"
    val subs = original.info.args.flatMap { case(name, width) =>
      List(name -> smt.BVSymbol(name + suffix, width), (name + "$prev") -> smt.BVSymbol(name + suffix + "$prev", width))
    } ++ original.info.rets.map{ case (name, width) => name -> smt.BVSymbol(name + suffix, width) } ++
      List(commitSignal -> smt.BVSymbol(commitSignal + suffix, 1))
    original.transitions.zipWithIndex.map { case (t,i) =>
      val copy = Transition(
        name = t.name + suffix,
        protocolName = t.protocolName,
        assertions = t.assertions.map(replace(_, subs)),
        assumptions = t.assumptions.map(replace(_, subs)),
        mappings = t.mappings.map(replace(_, subs)),
        ioAccess = t.ioAccess.map(replace(_, subs)),
        next = t.next.map(replace(_, subs))
      )
      s"${original.name}${suffix}@$i" -> copy
    }
  }
  private def replace(g: Next, subs: Map[String, smt.SMTExpr]): Next =
    g.copy(guard = g.guard.map(replace(_, subs)), commit = g.commit.map(replace(_, subs).asInstanceOf[smt.BVSymbol]))
  private def replace(g: GuardedAccess, subs: Map[String, smt.SMTExpr]): GuardedAccess =
    g.copy(guard = g.guard.map(replace(_, subs)))
  private def replace(g: GuardedMapping, subs: Map[String, smt.SMTExpr]): GuardedMapping =
    GuardedMapping(g.guard.map(replace(_, subs)), replace(g.arg, subs).asInstanceOf[smt.BVSymbol], g.bits, replace(g.update, subs))
  private def replace(g: Guarded, subs: Map[String, smt.SMTExpr]): Guarded =
    Guarded(g.guard.map(replace(_, subs)), replace(g.pred, subs))
  private def replace(e: smt.BVExpr, subs: Map[String, smt.SMTExpr]): smt.BVExpr =
    replaceSMT(e, subs).asInstanceOf[smt.BVExpr]
  private def replaceSMT(e: smt.SMTExpr, subs: Map[String, smt.SMTExpr]): smt.SMTExpr = e match {
    case s : smt.BVSymbol => subs.getOrElse(s.name, s)
    case other => other.mapExpr(replaceSMT(_, subs))
  }
}