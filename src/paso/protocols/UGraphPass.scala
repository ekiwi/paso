package paso.protocols

import scala.collection.mutable
import maltese.smt
import firrtl.ir


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
    val assumptions = n.actions.collect { case UAction(AAssume(cond), _, guard) => Guards.implies(guard, Guards.normalize(cond)) }.flatten
    if(assumptions.isEmpty) return n

    assert(n.next.nonEmpty, "Node has assumptions but no outgoing edges!")

    val otherActions = n.actions.filterNot(_.a.isInstanceOf[AAssume]).map(a => a.copy(guard = a.guard ++ assumptions))
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
    val nodes = g.nodes.map(onNode(g, _))
    // removing all asynchronous edges might leave some nodes unreachable
    RemoveUnreachable.run(g.copy(nodes = nodes))
  }

  private def onNode(g: UGraph, n: UNode): UNode = {
    // early exit
    if(n.next.forall(_.isSync)) return n

    // find all single step paths
    val paths = findSingleStepPaths(g, List(), n)
    val next = paths.map(p => UEdge(p.guard, isSync = true, to = p.to))
    val actions = paths.flatMap(_.actions)

    // ensure that there are no actions that depend on a fixed order
    actions.map(_.a).foreach {
      case _: ASet | _: AUnSet =>
        throw new RuntimeException(s"UnSet/Set commands are not supported in this pass! ${n}")
      case _ =>
    }

    n.copy(actions = actions, next = next)
  }

  private case class Path(actions: List[UAction], guard: List[smt.BVExpr], to: Int)
  private def findSingleStepPaths(g: UGraph, guard: List[smt.BVExpr], from: UNode): List[Path] = {
    val paths = from.next.flatMap { n =>
      if(n.isSync) {
        List(Path(List(), guard ++ n.guard, n.to))
      } else {
        findSingleStepPaths(g, guard ++ n.guard, g.nodes(n.to))
      }
    }
    val actions = from.actions.map(a => a.copy(guard = a.guard ++ guard))
    paths.map(p => p.copy(actions = actions ++ p.actions))
  }

}

/** Ensures that all outgoing edges are mutually exclusive.
 *  - uses a solver to filter out infeasible edges
 *  - could lead to exponential blowup
 *  - works only on a UGraph with only synchronous edges (this could probably be fixed)
 * */
class MakeDeterministic(solver: GuardSolver) extends UGraphPass {
  override def name: String = "MakeDeterministic"
  override def run(g: UGraph): UGraph = {
    // visited is also used to lookup the id of the new combined nodes
    val visited = mutable.HashMap[NodeKey, Int]()
    val todo = mutable.Stack[NodeKey]()
    val newNodes = mutable.ArrayBuffer[UNode]()

    // start
    visited(Set(0)) = 0
    todo.push(Set(0))

    while(todo.nonEmpty) {
      // we sort the set in order to ensure deterministic behavior
      val nodes = todo.pop().toList.sorted.map(g.nodes)

      // combine all actions together
      val actions = nodes.flatMap(_.actions)
      val name = nodes.map(_.name).mkString(" and ")

      // the edges could be mutually exclusive but do not have to be
      val edges = nodes.flatMap(_.next)
      val next = mergeEdges(edges).map { case (guard, to) =>
        val id = visited.getOrElseUpdate(to, {
          // if we haven't seen this combination yet
          todo.push(to)
          visited.size
        })
        UEdge(guard, isSync = true, to=id)
      }

      // save new node
      newNodes.append(UNode(name, actions, next))
    }

    g.copy(nodes = newNodes.toIndexedSeq)
  }

  private type NodeKey = Set[Int]
  private type Guard = List[smt.BVExpr]

  // assumes that the edges on their own are feasible
  private def mergeEdges(next: List[UEdge]): List[(Guard, NodeKey)] = {
    assert(next.forall(_.isSync))
    if(next.isEmpty) return List()

    val remainingEdges = mutable.Stack[UEdge]()
    next.foreach(remainingEdges.push)

    val firstEdge = remainingEdges.pop()
    var finalEdges = List((firstEdge.guard, Set(firstEdge.to)))

    // merge edges until there aren't any left
    while(remainingEdges.nonEmpty) {
      val newEdge = remainingEdges.pop()
      val feasible = finalEdges.flatMap { case (oldGuard, oldNext) =>
        // TODO: better guard simplification
        List(
          (Guards.not(oldGuard) ++ newEdge.guard, Set(newEdge.to)),
          (oldGuard ++ Guards.not(newEdge.guard), oldNext),
          (oldGuard ++ newEdge.guard, oldNext ++ Set(newEdge.to)),
        )
        // simplify guards and filter out infeasible edges
          .map { case (guard, next) => (solver.simplify(guard), next) }
          .filter { case (guard, _) => solver.isSat(guard) }
      }

      // merge edges with same target
      val merged = feasible.groupBy(_._2).toList.map { case (next, guards) =>
        if(guards.size == 1) { guards.head } else {
          // either edge will take us to the same state:
          val combined = solver.simplify(guards.map(_._1).reduce((a,b) => Guards.or(a, b)))
          (combined, next)
        }
      }

      // update edges
      finalEdges = merged
    }

    finalEdges
  }
}

/** Tries to reduce the number of individual actions per node by merging actions. */
class MergeActions(solver: GuardSolver)  extends UGraphPass {
  override def name: String = "MergeActions"
  override def run(g: UGraph): UGraph = {
    val nodes = g.nodes.map(onNode)
    g.copy(nodes = nodes)
  }

  private def onNode(n: UNode): UNode = {
    val byAction = n.actions.groupBy(_.a).toList
    // exit early if there are no actions that can be merged
    if(byAction.size == n.actions.size) return n

    val actions = byAction.map { case (a, actions) =>
      val infos = actions.map(_.info).toSet.toSeq
      val info = if(infos.length > 1) ir.MultiInfo(infos) else infos.head
      val guard = solver.simplify(actions.map(_.guard).reduce((a,b) => Guards.or(a, b)))
      UAction(a, info, guard)
    }

    n.copy(actions = actions)
  }
}