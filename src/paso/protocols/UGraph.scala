// Copyright 2020-2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>


package paso.protocols

import firrtl.backends.experimental.smt.ExpressionConverter
import firrtl.ir
import maltese.bdd.BDDToSMTConverter
import maltese.smt

import scala.collection.mutable

/** This is an attempt at coming up with a unified graph representation for protocols */
case class UGraph(name: String, nodes: IndexedSeq[UNode]) {
  def size: Int = nodes.size
}
case class UAction(a: Action, info: ir.Info, guard: smt.BVExpr = smt.True())
case class UEdge(to: Int, isSync: Boolean, guard: smt.BVExpr = smt.True())
case class UNode(name: String, actions: List[UAction] = List(), next: List[UEdge] = List())

sealed trait Action
case class ASignal(name: String) extends Action
case class ASet(input: String, rhs: smt.BVExpr, isSticky: Boolean) extends Action
case class AUnSet(input: String) extends Action
case class AAssert(cond: smt.BVExpr) extends Action
case class AAssume(cond: smt.BVExpr) extends Action
case class AInputAssign(pin: String) extends Action
case class AMapping(arg: smt.BVSymbol, hi: Int, lo: Int, update: smt.BVExpr) extends Action {
  def bits: BigInt = BitMapping.toMask(hi, lo)
  def mapsAll: Boolean = lo == 0 && (hi == arg.width - 1)
}

object Action {
  def serialize(a: Action): String = a match {
    case ASignal(name) => name
    case ASet(input, rhs, _) => s"set($input := $rhs)"
    case AUnSet(input) => s"unset($input)"
    case AAssert(cond) => s"assert($cond)"
    case AAssume(cond) => s"assume($cond)"
    case AInputAssign(pin) => s"assign($pin)"
    case a @ AMapping(arg, _, _, update) if a.mapsAll => s"map($arg := $update)"
    case AMapping(arg, hi, lo, update) => s"map($arg[$hi,$lo] := $update)"
  }
}


/** turns a GOTO program into a UGraph */
class UGraphConverter(protocol: firrtl.CircuitState, stickyInputs: Boolean)
  extends ProtocolInterpreter(protocol, stickyInputs) {

  private val nodes = mutable.ArrayBuffer[UNode]()

  def run(name: String): UGraph = {
    // start with no nodes
    nodes.clear()

    // add a node for every target
    nodes.append(UNode("start"))
    (1 until blockCount).foreach { id =>
      assert(nodes.length == id)
      nodes.append(UNode(s"block$id"))
    }

    // convert instructions
    val finalNode = (0 until blockCount).map(convertBlock).filter(_ >= 0)

    // rename final node to "end"
    finalNode match {
      case Seq(index) => nodes(index) = nodes(index).copy(name = "end")
      case other => throw new RuntimeException(s"Expecting exactly one final node! $other")
    }

    UGraph(name, nodes)
  }

  private def convertBlock(id: Int): Int = {
    val stmts = getBlock(id).map{ case (l, s) => parseStmt(s, l) }
    var head = id
    stmts.foreach {
      case s: DoStep =>
        // add step (synchronous) edge
        val next = addNode()
        addToNode(head, List(), List(UEdge(to = next, isSync = true)))
        head = next
        // add Fork edge if necessary
        head = if(steps(s.name).doFork) addAction(head, ASignal("fork"), s.info) else head
      case s: DoSet =>
        val rhs = toSMT(s.expr, inputs(s.loc), allowNarrow = true)
        head = addAction(head, ASet(s.loc, rhs, s.isSticky), s.info)
      case s: DoUnSet => head = addAction(head, AUnSet(s.loc), s.info)
      case s: DoAssert => head = addAction(head, AAssert(toSMT(s.expr)), s.info)
      case s: Goto =>
        addBranch(head, toSMT(s.cond), s.getTargets)
        head = -1 // should be the end of the block
    }
    head
  }

  private def toSMT(expr: ir.Expression, width: Int = 1, allowNarrow: Boolean = false): smt.BVExpr = {
    val raw = ExpressionConverter.toMaltese(expr, width, allowNarrow)
    smt.SMTSimplifier.simplify(raw).asInstanceOf[smt.BVExpr]
  }

  private def addBranch(startId: Int, cond: smt.BVExpr, targets: List[Int]): Unit = targets match {
    case List(to) =>
      addToNode(startId, edges = List(UEdge(to, isSync = false)))
    case List(toTru, toFals) =>
      val truCond = Guards.simplify(cond)
      val falsCond = Guards.simplify(smt.BVNot(cond))
      val edges = List(
        UEdge(toTru, isSync = false, truCond),
        UEdge(toFals, isSync = false, falsCond),
      )
      addToNode(startId, edges=edges)
  }

  private def addAction(startId: Int, a: Action, info: ir.Info): Int = {
    val actions = List(UAction(a, info))
    val e = UEdge(to = addNode(), isSync = false)
    addToNode(startId, actions, List(e))
    e.to
  }

  private def addToNode(id: Int, actions: List[UAction] = List(), edges: List[UEdge] = List()): Unit = {
    val n = nodes(id)
    nodes(id) = n.copy(actions = n.actions ++ actions, next = n.next ++ edges)
  }

  private def addNode(name: String = ""): Int = {
    val id = nodes.length
    nodes.append(UNode(name, List()))
    id
  }
}

/** Guards are represented as a list of "clauses", an empty list means true! */
object Guards {
  def simplify(g: smt.BVExpr): smt.BVExpr = smt.SMTSimplifier.simplify(g).asInstanceOf[smt.BVExpr]
}

class GuardSolver(solver: smt.Solver) {
  private val conv = new BDDToSMTConverter()
  def isSat(guard: smt.BVExpr): Boolean = {
    val norm = simplify(guard)
    // an empty list means "true" and "true" is trivially SAT
    if(norm == smt.True()) { true } else {
      solver.check(norm).isSat
    }
  }
  def simplify(guard: smt.BVExpr): smt.BVExpr = {
    if(guard == smt.True()) return guard
    val norm = Guards.simplify(guard)
    val bdd = conv.smtToBdd(norm)
    conv.bddToSmt(bdd)
  }

}

class UGraphBuilder(name: String) {
  private val nodes = mutable.ArrayBuffer[UNode]()
  def addNode(name: String, actions: List[UAction] = List()): Int = {
    val node = UNode(name, actions)
    val id = size
    nodes.append(node)
    id
  }

  /** returns the new id of the starting state */
  def addGraph(g: UGraph): Int = {
    val shift = size
    g.nodes.foreach { n =>
      val next = n.next.map(n => n.copy(to = n.to + shift))
      nodes.append(n.copy(next=next))
    }
    shift
  }

  def addEdge(from: Int, to: Int): Unit = {
    assert(to >= 0 && to < size)
    addEdge(from, UEdge(to, isSync = false))
  }

  def addSyncEdge(from: Int, to: Int): Unit = {
    assert(to >= 0 && to < size)
    addEdge(from, UEdge(to, isSync = true))
  }

  def addEdge(from: Int, e: UEdge): Unit = {
    assert(from >= 0 && from < size)
    val n = nodes(from)
    nodes(from) = n.copy(next = n.next :+ e)
  }

  def get: UGraph = UGraph(name, nodes.toIndexedSeq)
  def size: Int = nodes.size
}