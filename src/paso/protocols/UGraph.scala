// Copyright 2020-2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>


package paso.protocols

import firrtl.backends.experimental.smt.ExpressionConverter
import firrtl.ir
import maltese.smt
import scala.collection.mutable

/** This is an attempt at coming up with a unified graph representation for protocols */
case class UGraph(name: String, nodes: IndexedSeq[UNode])
case class UAction(a: Action, info: ir.Info, guard: List[smt.BVExpr] = List())
case class UEdge(guard: List[smt.BVExpr], isSync: Boolean, to: Int)
case class UNode(name: String, actions: List[UAction] = List(), next: List[UEdge] = List())

sealed trait Action
case class ASignal(name: String) extends Action
case class ASet(input: String, rhs: smt.BVExpr) extends Action
case class AUnSet(input: String) extends Action
case class AAssert(cond: List[smt.BVExpr]) extends Action
case class AIOAccess(pin: String, bits: BigInt) extends Action
case class AMapping(arg: smt.BVSymbol, hi: Int, lo: Int, update: smt.BVExpr) extends Action {
  def bits: BigInt = BitMapping.toMask(hi, lo)
  def mapsAll: Boolean = lo == 0 && (hi == arg.width - 1)
}

object Action {
  def serialize(a: Action): String = a match {
    case ASignal(name) => name
    case ASet(input, rhs) => s"set($input := $rhs)"
    case AUnSet(input) => s"unset($input)"
    case AAssert(cond) => s"assert(${smt.BVAnd(cond)}"
    case AIOAccess(pin, bits) => s"access($pin)"
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
        addToNode(head, List(), List(UEdge(List(), isSync = true, to = next)))
        head = next
        // add Fork edge if necessary
        head = if(steps(s.name).doFork) addAction(head, ASignal("fork"), s.info) else head
      case s: DoSet =>
        val rhs = toSMT(s.expr, inputs(s.loc), allowNarrow = true)
        head = addAction(head, ASet(s.loc, rhs), s.info)
      case s: DoUnSet => head = addAction(head, AUnSet(s.loc), s.info)
      case s: DoAssert => head = addAction(head, AAssert(List(toSMT(s.expr))), s.info)
      case s: Goto =>
        addBranch(head, List(toSMT(s.cond)), s.getTargets)
        head = -1 // should be the end of the block
    }
    head
  }

  private def toSMT(expr: ir.Expression, width: Int = 1, allowNarrow: Boolean = false): smt.BVExpr = {
    ExpressionConverter.toMaltese(expr, width, allowNarrow)
  }

  private def addBranch(startId: Int, cond: List[smt.BVExpr], targets: List[Int]): Unit = targets match {
    case List(to) =>
      addToNode(startId, edges = List(UEdge(List(), isSync = false, to)))
    case List(toTru, toFals) =>
      val truCond = Guards.normalize(cond)
      val falsCond = Guards.not(cond)
      val edges = List(
        UEdge(truCond, isSync = false, to = toTru),
        UEdge(falsCond, isSync = false, to = toFals),
      )
      addToNode(startId, edges=edges)
  }

  private def addAction(startId: Int, a: Action, info: ir.Info): Int = {
    val actions = List(UAction(a, info))
    val e = UEdge(List(), isSync = false, to = addNode())
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

/** checks which bits are mopped */
object MappedBitsAnalysis {

}

/** turn Set actions into assumptions and Map actions */
object ConvertSet {
  def run(g: UGraph): UGraph = {
    ???
  }
}

/** Guards are represented as a list of "clauses", an empty list is means true! */
object Guards {
  def not(g: List[smt.BVExpr]): List[smt.BVExpr] = {
    List(smt.BVNot(smt.BVAnd(g)))
  }
  def normalize(g: List[smt.BVExpr]): List[smt.BVExpr] = {
    val simpl = g.map(simplify).flatMap(splitConjunction)
    removeDuplicates(simpl)
  }
  private def simplify(e: smt.BVExpr): smt.BVExpr = smt.SMTSimplifier.simplify(e).asInstanceOf[smt.BVExpr]
  private def splitConjunction(e: smt.BVExpr): List[smt.BVExpr] = e match {
    case smt.BVAnd(a, b) => splitConjunction(a) ++ splitConjunction(b)
    case other => List(other)
  }
  private def removeDuplicates(es: List[smt.BVExpr]): List[smt.BVExpr] = {
    if(es.length <= 1) return es
    val positive = mutable.HashSet[String]()
    val negative = mutable.HashSet[String]()
    es.flatMap {
      case o @ smt.BVNot(n) =>
        val key = n.toString
        // if we have the same expression in positive form -> the conjunction is trivially false
        if(positive.contains(key)) return List(smt.False())
        val duplicate = negative.contains(key)
        negative.add(key)
        if(duplicate) None else Some(o)
      case p =>
        val key = p.toString
        // if we have the same expression in negative form -> the conjunction is trivially false
        if(negative.contains(key)) return List(smt.False())
        val duplicate = positive.contains(key)
        positive.add(key)
        if(duplicate) None else Some(p)
    }
  }
}