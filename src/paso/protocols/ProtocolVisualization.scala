// Copyright 2020-2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import maltese.smt.BVAnd

import java.io._
import scala.sys.process._

object ProtocolVisualization {
  val DefaultNodeShape = "point"

  def toDot(g: ProtocolGraph): String = {
    val nodes = g.transitions.zipWithIndex.map { case (t, i) =>
      s"""  $i [shape=$DefaultNodeShape,label="${t.name}"]"""
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


  def showDot(src: String, fileName: String = "test.dot"): Unit = {
    val ff = new FileWriter(fileName)
    ff.write(src)
    ff.close()
    val cmd = s"xdot $fileName"
    println(s"Launching: $cmd")
    cmd.!!
  }

  def showDot(graph: ProtocolGraph): Unit = showDot(toDot(graph))
}
