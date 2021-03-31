// Copyright 2020-2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import maltese.smt

import java.io._
import scala.sys.process._

object ProtocolVisualization {
  val DefaultNodeShape = "box"

  private def implies(guard: List[smt.BVExpr], rhs: String): String = {
    if(guard.isEmpty) { rhs } else {
      smt.BVAnd(guard).toString + " => " + rhs
    }
  }

  private def implies(guard: smt.BVExpr, rhs: String): String = {
    if(guard == smt.True()) { rhs } else { guard + " => " + rhs }
  }

  private def serialize(a: UAction, includeInfo: Boolean): String = {
    val s = implies(a.guard, Action.serialize(a.a))
    if(includeInfo) s + a.info.serialize else s
  }

  val SyncEdgeStyle = """color = "black:invis:black""""
  def toDot(g: UGraph, includeInfo: Boolean = false): String = {
    val nodes = g.nodes.zipWithIndex.map { case (t, i) =>
      val name = s"[$i] ${t.name}"
      val lines = List(name) ++ t.actions.map(serialize(_, includeInfo))
      val label = lines.mkString("\\n")
      s"""  $i [shape=$DefaultNodeShape,label="$label"]"""
    }
    val edges = g.nodes.zipWithIndex.flatMap { case (t, from) =>
      t.next.map { n =>
        val guard = if(n.guard == smt.True()) None else Some("[" + n.guard.toString + "]")
        val lbl = guard.getOrElse("")
        val style = if(n.isSync) "," + SyncEdgeStyle else ""
        s"""  $from -> ${n.to} [label="$lbl"$style]"""
      }
    }

    s"""digraph "${g.name}" {
       |
       |${nodes.map(_ + ";").mkString("\n")}
       |${edges.map(_ + ";").mkString("\n")}
       |}
       |""".stripMargin
  }


  def saveDot(src: String, fileName: String): Unit = {
    val ff = new FileWriter(fileName)
    ff.write(src)
    ff.close()
  }
  def saveDot(g: UGraph, includeInfo: Boolean, fileName: String, maxNodes: Int = 100): Unit ={
    if(g.nodes.size <= maxNodes) {
      saveDot(toDot(g, includeInfo), fileName)
    }
  }

  def showDot(src: String, fileName: String = "test.dot"): Unit = {
    saveDot(src, fileName)
    val cmd = s"xdot $fileName"
    println(s"Launching: $cmd")
    cmd.!!
  }

  def showDot(graph: UGraph): Unit = showDot(toDot(graph))
}
