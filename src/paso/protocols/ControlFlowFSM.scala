// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import maltese.smt

/** The complete control flow of all protocols combined into a single fsm using sequential composition + forking */
case class ControlFlowFSM()


object ControlFlowFSM {
  case class Loc(name: String, transitions: Int, copy: Int = 0) {
    def instance: String = s"$name$$$copy"
    def tran: String = s"$name@$transitions"
    override def toString: String = s"$name$$$copy@$transitions"
  }
  case class State(id: Int, active: Iterable[Loc], fork: Boolean)
  case class Next(guard: smt.BVExpr, )

  def encode(protocols: Iterable[ProtocolGraph]): ControlFlowFSM = {
    val transitions = protocols.flatMap(p => p.transitions.zipWithIndex.map{ case (t,i) =>
      s"${p.name}@$i" -> t
    })
    // TODO: check that protocols are mutually exclusive!
    ???
  }

  private def onState(st: State, protocols: Iterable[ProtocolGraph], transitions: Map[String, Transition]): Unit = {
    // we assume that any protocol copy can only be active once in a single state
    assert(st.active.map(_.instance).toSet.size == st.active.size)

    // new locations start executing in parallel with any active protocols
    val newLocs = if(st.fork) fork(st.active, protocols) else List()

    // first we check to make sure that all current transitions are compatible with each other
    // TODO: actually check

    // determine all new states
    val nextStates = newLocs.zipWithIndex.flatMap { case (newLoc, forkId) =>


    }


  }

  private def ensureCompatible(aProt: String, a: Transition, bProt: String, b: Transition): Unit = {
    // TODO
  }

  private def fork(active: Iterable[Loc], protocols: Iterable[ProtocolGraph]): Iterable[Loc] =
    protocols.map { p => Loc(p.name, 0, getFreeCopy(p.name, active)) }

  private def getFreeCopy(name: String, active: Iterable[Loc]): Int = {
    val activeIds = active.filter(_.name == name).map(_.copy).toSet
    Iterator.from(0).find(ii => !activeIds.contains(ii)).get
  }
}