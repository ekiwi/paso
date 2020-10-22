// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import maltese.smt

/** The complete control flow of all protocols combined into a single fsm using sequential composition + forking */
case class ControlFlowFSM()


object ControlFlowFSM {
  case class Loc(name: String, transition: Int, copyId: Int = 0) {
    def instance: String = s"$name$$$copyId"
    def tran: String = s"$name@$transition"
    override def toString: String = s"$name$$$copyId@$transition"
  }
  case class State(id: Int, active: Iterable[Loc], fork: Boolean)
  case class Next(guard: smt.BVExpr, state: Int)

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

    // determine all new states
    val nextStates = newLocs.flatMap { newLoc =>
      product(st.active.map(getNonFinalNext(_, transitions)).toSeq).map { otherLocs =>
        val active = otherLocs :+ newLoc
        println(active)
      }
    }


  }

  private def ensureCompatible(aProt: String, a: Transition, bProt: String, b: Transition): Unit = {
    // TODO
  }

  private def getNonFinalNext(loc: Loc, transitions: Map[String, Transition]): Seq[Loc] =
    transitions(loc.tran).next.filterNot(_.isFinal).map(n => loc.copy(transition = n.cycleId))

  private def getNext(loc: Loc, transitions: Map[String, Transition]): Seq[Loc] =
    transitions(loc.tran).next.map(n => loc.copy(transition = n.cycleId))

  private def fork(active: Iterable[Loc], protocols: Iterable[ProtocolGraph]): Iterable[Loc] =
    protocols.map { p => Loc(p.name, 0, getFreeCopy(p.name, active)) }

  private def getFreeCopy(name: String, active: Iterable[Loc]): Int = {
    val activeIds = active.filter(_.name == name).map(_.copyId).toSet
    Iterator.from(0).find(ii => !activeIds.contains(ii)).get
  }

  // https://stackoverflow.com/questions/8321906/lazy-cartesian-product-of-several-seqs-in-scala/8569263
  private def product[N](xs: Seq[Seq[N]]): Seq[Seq[N]] =
    xs.foldLeft(Seq(Seq.empty[N])){ (x, y) => for (a <- x.view; b <- y) yield a :+ b }
}