package paso.protocols

import scala.collection.mutable


trait UGraphPass {
  def name: String
  def run(g: UGraph): UGraph
}

/** Turns assumptions in a node into guards on all outgoing edges.
 *  This makes sense if we accept an implicit assumption that at least one of the
 *  outgoing edges (for a DFA, exactly one) will be feasible.
 *  This pass will fail if a node has an assumption, but no outgoing edge.
 * */
object AssumptionsToGuards extends UGraphPass {
  override def name = "AssumptionsToGuards"

  override def run(g: UGraph): UGraph = {
    val nodes = g.nodes.map(onNode)
    g.copy(nodes = nodes)
  }

  private def onNode(n: UNode): UNode = {
    val assumptions = n.actions.collect { case UAction(AAssume(cond), _, guard) => Guards.implies(guard, cond) }.flatten
    if(assumptions.isEmpty) return n

    assert(n.next.nonEmpty, "Node has assumptions but no outgoing edges!")

    val otherActions = n.actions.filterNot(_.a.isInstanceOf[AAssume])
    val next = n.next.map(e => e.copy(guard = e.guard ++ assumptions))

    n.copy(actions = otherActions, next = next)
  }
}

/** Removes any nodes that are unreachable.
 *  WARN: Does not take guard feasibility into account!
 *        Thus if a node is only reachable through an unfeasible edge, it will still be kept around.
 * */
object RemoveUnreachable extends UGraphPass {
  override def name: String = "RemoveUnreachable"
  override def run(g: UGraph): UGraph = {
    var visited = Set(0)
    val todo = mutable.Stack(0)

    while(todo.nonEmpty) {
      val node = g.nodes(todo.pop())
      val next = node.next.map(_.to).toSet.toSeq.filterNot(visited.contains)
      next.foreach(todo.push)
      visited ++= next
    }

    if(visited.size < g.nodes.size) {
      // if there are unreachable nodes, we need to compact the graph
      compact(g, visited)
    } else { g }
  }

  private def compact(g: UGraph, visited: Iterable[Int]): UGraph = {
    val remaining = visited.toIndexedSeq.sorted
    val idMap = remaining.zipWithIndex.toMap
    val nodes = remaining.map(g.nodes).map(onNode(_, idMap))
    g.copy(nodes = nodes)
  }

  private def onNode(n: UNode, idMap: Map[Int, Int]): UNode = {
    val next = n.next.map(e => e.copy(to = idMap(e.to)))
    n.copy(next = next)
  }
}

/** Removes all edges where isSync=false.
 *  Requirements:
 *  - no order sensitive Actions: ASet, AUnSet
 *  - no cycles along isSync=false edges
 */
object RemoveAsynchronousEdges extends UGraphPass {
  override def name: String = "RemoveAsynchronousEdges"
  override def run(g: UGraph): UGraph = {
    val nodes = g.nodes.map(onNode)
    // removing all asynchronous edges might leave some nodes unreachable
    RemoveUnreachable.run(g.copy(nodes = nodes))
  }

  private def onNode(n: UNode): UNode = {
    n.actions.map(_.a).foreach {
      case _: ASet | _: AUnSet =>
        throw new RuntimeException(s"UnSet/Set commands are not supported in this pass! ${n}")
      case _ =>
    }

    ???

  }

}

/** Ensures that all outgoing edges are mutually exclusive.
 *  - uses a solver to filter out infeasible edges
 *  - could lead to exponential blowup
 *  - works only on a UGraph with only synchronous edges (this could probably be fixed)
 * */
object MakeDeterministic extends UGraphPass {
  override def name: String = "MakeDeterministic"
  override def run(g: UGraph): UGraph = {
    ???
  }
}