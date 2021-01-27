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
case class UAction(name: String, guard: List[smt.BVExpr])
case class UEdge(guard: List[smt.BVExpr], isSync: Boolean, to: Int)
case class UNode(name: String, actions: List[UAction], next: List[UEdge])


/** turns a GOTO program into a UGraph */
class UGraphConverter(protocol: firrtl.CircuitState, stickyInputs: Boolean)
  extends ProtocolInterpreter(protocol, stickyInputs) {

  private val nodes = mutable.ArrayBuffer[UNode]()

  def run(name: String): UGraph = {
    // start with no nodes
    nodes.clear()

    // add a node for every target
    nodes.append(UNode("start", List(), List()))
    (1 until blockCount).foreach { id =>
      assert(nodes.length == id)
      nodes.append(UNode(s"block$id", List(), List()))
    }
    nodes.append(UNode("end", List(), List()))

    // convert instructions
    (0 until blockCount).foreach(convertBlock)

    UGraph(name, nodes)
  }

  private def convertBlock(id: Int): Unit = {
    val stmts = getBlock(id).map{ case (l, s) => parseStmt(s, l) }
    var head = id
    stmts.foreach {
      case s: DoStep => head = addAction(head, "step", isSync = true)
      case s: DoSet => head = addAction(head, s"set(${s.loc} := ${s.expr})")
      case s: DoUnSet => head = addAction(head, s"unset(${s.loc})")
      case s: DoAssert => head = addAction(head, s"assert(${s.expr})")
      case s: Goto =>
        addBranch(head, condToSmt(s.cond), s.getTargets)
        head = -1 // should be the end of the block
    }
  }

  private def condToSmt(e: ir.Expression): List[smt.BVExpr] = {
    List(ExpressionConverter.toMaltese(e, 1, allowNarrow = false))
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

  private def addAction(startId: Int, name: String, isSync: Boolean = false): Int = {
    val a = UAction(name, List())
    val e = UEdge(List(), isSync = isSync, to = addNode())
    addToNode(startId, List(a), List(e))
    e.to
  }

  private def addToNode(id: Int, actions: List[UAction] = List(), edges: List[UEdge] = List()): Unit = {
    val n = nodes(id)
    nodes(id) = n.copy(actions = n.actions ++ actions, next = n.next ++ edges)
  }

  private def addNode(name: String = ""): Int = {
    val id = nodes.length
    nodes.append(UNode(name, List(), List()))
    id
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