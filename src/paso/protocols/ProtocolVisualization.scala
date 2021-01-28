// Copyright 2020-2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import maltese.smt.{BVAnd, BVExpr}

import java.io._
import scala.sys.process._

object ProtocolVisualization {
  val DefaultNodeShape = "box"

  private def implies(guard: List[BVExpr], rhs: String): String = {
    if(guard.isEmpty) { rhs } else {
      BVAnd(guard).toString + " => " + rhs
    }
  }

  def serialize(a: Guarded): String = implies(a.guard, a.pred.toString)

  def serialize(m: GuardedMapping): String = {
    val allBits = ((BigInt(1) << m.arg.width) - 1) == m.bits
    val variable = if(allBits) m.arg.name else m.arg.name + "[" + m.bits.toString(2) + "]"
    implies(m.guard, s"($variable <-> ${m.update})")
  }


  def toDot(g: ProtocolGraph): String = {
    val nodes = g.transitions.zipWithIndex.map { case (t, i) =>
      val lines = List(t.name) ++
        t.assumptions.map(serialize).map("Assume(" + _ + ")") ++
        t.mappings.map(serialize) ++
        t.assertions.map(serialize).map("Assert(" + _ + ")")
      val label = lines.filter(_.nonEmpty).mkString("\\n")
      s"""  $i [shape=$DefaultNodeShape,label="$label"]"""
    }
    val edges = g.transitions.zipWithIndex.flatMap { case (t, i) =>
      t.next.map { n =>
        val guard = if(n.guard.isEmpty) "" else BVAnd(n.guard).toString
        val attributes = n.commit.map(_.name) ++
          (if(n.fork) Some("fork") else None) ++
          (if(n.isFinal) Some("final") else None)
        val lbl = guard + attributes.mkString("(", " + ", ")")
        s"""  $i -> ${n.cycleId} [label="$lbl"]"""
      }
    }

    s"""digraph "${g.name}" {
      |  rankdir="LR";
      |${nodes.map(_ + ";").mkString("\n")}
      |${edges.map(_ + ";").mkString("\n")}
      |}
      |""".stripMargin
  }

  private def serialize(a: UAction, includeInfo: Boolean): String = {
    val s = implies(a.guard, Action.serialize(a.a))
    if(includeInfo) s + a.info.serialize else s
  }

  val SyncEdgeStyle = """color = "black:invis:black""""
  def toDot(g: UGraph, includeInfo: Boolean = false): String = {
    val nodes = g.nodes.zipWithIndex.map { case (t, i) =>
      val name = if(t.name.nonEmpty) Some("# " + t.name) else None
      val lines = name ++ t.actions.map(serialize(_, includeInfo))
      val label = lines.mkString("\\n")
      s"""  $i [shape=$DefaultNodeShape,label="$label"]"""
    }
    val edges = g.nodes.zipWithIndex.flatMap { case (t, from) =>
      t.next.map { n =>
        val guard = if(n.guard.isEmpty) None else Some("[" + BVAnd(n.guard).toString + "]")
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


  def showDot(src: String, fileName: String = "test.dot"): Unit = {
    val ff = new FileWriter(fileName)
    ff.write(src)
    ff.close()
    val cmd = s"xdot $fileName"
    println(s"Launching: $cmd")
    cmd.!!
  }

  def showDot(graph: ProtocolGraph): Unit = showDot(toDot(graph))
  def showDot(graph: UGraph): Unit = showDot(toDot(graph))
}
