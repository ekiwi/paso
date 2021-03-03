package paso.protocols

import scala.collection.mutable
import maltese.smt
import firrtl.ir


trait UGraphPass {
  def name: String
  def run(g: UGraph): UGraph
}

object UGraphPass {
  def mergeInfo(i: Seq[ir.Info]): ir.Info = if(i.length > 1) ir.MultiInfo(i) else i.head
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
    val assumptions = n.actions.collect { case UAction(AAssume(cond), _, guard) => smt.BVImplies(guard, cond) }
    if(assumptions.isEmpty) return n

    assert(n.next.nonEmpty, "Node has assumptions but no outgoing edges!")

    val assumption = Guards.simplify(smt.BVAnd(assumptions))
    val otherActions = n.actions.filterNot(_.a.isInstanceOf[AAssume]).map(a => a.copy(guard = smt.BVAnd(assumption, a.guard)))
    val next = n.next.map(e => e.copy(guard = smt.BVAnd(assumption, e.guard)))

    n.copy(actions = otherActions, next = next)
  }
}

/** Tries to undo Assumptions to Guards */
class GuardsToAssumptions(solver: GuardSolver)  extends UGraphPass {
  override def name = "GuardsToAssumptions"

  override def run(g: UGraph): UGraph = {
    val nodes = g.nodes.map(onNode)
    g.copy(nodes = nodes)
  }

  private def onNode(n: UNode): UNode = {
    // in case there are already assumptions in the node
    val assumptions = n.actions.collect{ case UAction(AAssume(cond), _, guard) => smt.BVImplies(guard, cond) }

    // the implicit assumption is that (at least) one of the outgoing edges is true
    // special exception: no outgoing edges
    val outgoingEdgeAssumption =
      if(n.next.isEmpty) smt.True() else solver.simplify(n.next.map(_.guard).reduce(smt.BVOr(_, _)))
    val allAssumptions = if(assumptions.isEmpty) { outgoingEdgeAssumption } else {
      solver.simplify(smt.BVAnd(assumptions :+ outgoingEdgeAssumption))
    }

    // filter out common clauses from actions
    val assumptionClauses = destructAnd(allAssumptions).toSet
    val actions = n.actions.map(removeClauses(assumptionClauses, _))

    // filter out common clauses from edges
    val next = n.next.map(removeClauses(assumptionClauses, _))

    // turns common edge assumptions into actions
    val edgeAssumptions =
      if(n.next.isEmpty) List() else destructAnd(outgoingEdgeAssumption).map(cond => UAction(AAssume(cond), ir.NoInfo))

    n.copy(actions = actions ++ edgeAssumptions, next= next)
  }

  // remove common clauses from the action guard
  private def removeClauses(clauses: Set[smt.BVExpr], a: UAction): UAction = {
    if(a.guard == smt.True()) return a
    val guardClauses = destructAnd(a.guard).filterNot(clauses.contains)
    a.copy(guard = guardClauses.foldLeft[smt.BVExpr](smt.True())(smt.BVAnd(_, _)))
  }
  private def removeClauses(clauses: Set[smt.BVExpr], e: UEdge): UEdge = {
    if(e.guard == smt.True()) return e
    val guardClauses = destructAnd(e.guard).filterNot(clauses.contains)
    e.copy(guard = guardClauses.foldLeft[smt.BVExpr](smt.True())(smt.BVAnd(_, _)))
  }

  private def destructAnd(e: smt.BVExpr): List[smt.BVExpr] = e match {
    case smt.BVAnd(a, b) => destructAnd(a) ++ destructAnd(b)
    case other => List(other)
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
    // first we try to remove simple forwarding states
    val noForwarding = RemoveForwardingStates.run(g)

    val nodes = noForwarding.nodes.map(onNode(g, _))
    // removing all asynchronous edges might leave some nodes unreachable
    RemoveUnreachable.run(noForwarding.copy(nodes = nodes))
  }

  private def onNode(g: UGraph, n: UNode): UNode = {
    // early exit
    if(n.next.forall(_.isSync)) return n

    // find all single step paths
    val paths = findSingleStepPaths(g, smt.True(), n)
    val next = paths.map(p => UEdge(to = p.to, isSync = true, p.guard))
    val actions = paths.flatMap(_.actions)

    // ensure that there are no actions that depend on a fixed order
    actions.map(_.a).foreach {
      case _: ASet | _: AUnSet =>
        throw new RuntimeException(s"UnSet/Set commands are not supported in this pass! ${n}")
      case _ =>
    }

    n.copy(actions = actions, next = next)
  }

  private case class Path(actions: List[UAction], guard: smt.BVExpr, to: Int)
  private def findSingleStepPaths(g: UGraph, guard: smt.BVExpr, from: UNode): List[Path] = {
    val paths = from.next.flatMap { n =>
      if(n.isSync) {
        List(Path(List(), smt.BVAnd(guard, n.guard), n.to))
      } else {
        findSingleStepPaths(g, smt.BVAnd(guard, n.guard), g.nodes(n.to))
      }
    }
    val actions = from.actions.map(a => a.copy(guard = smt.BVAnd(guard, a.guard)))
    paths.map(p => p.copy(actions = actions ++ p.actions))
  }

}

/** Removes all states that have:
 *  - no actions
 *  - a single async outgoing edge with no guard
 * */
object RemoveForwardingStates extends UGraphPass {
  override def name: String = "RemoveForwardingStates"
  override def run(g: UGraph): UGraph = {
    val forwards = g.nodes.indices.map( i => i -> onNode(g, i) )
    if(forwards.forall(f => f._1 == f._2)) return g
    val forwardMap = forwards.toMap
    g.copy(nodes = g.nodes.map(changeEdges(_, forwardMap)))
  }

  private def changeEdges(n: UNode, forwards: Map[Int, Int]): UNode = {
    n.copy(next = n.next.map(e => e.copy(to = forwards(e.to))))
  }

  private def onNode(g: UGraph, id: Int): Int = {
    val n = g.nodes(id)
    val isForwardingState = n.actions.isEmpty && n.next.size == 1 && (n.next.head.guard == smt.True()) && !n.next.head.isSync
    if(isForwardingState) {
      // forward to next node (which might be a forwarding node itself)
      onNode(g, n.next.head.to)
    } else {
      id
    }
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
    val newNodes = mutable.ArrayBuffer[(Int, UNode)]()

    // start
    visited(Set(0)) = 0
    todo.push(Set(0))

    while(todo.nonEmpty) {
      // we sort the set in order to ensure deterministic behavior
      val key = todo.pop()
      val nodes = key.toList.sorted.map(g.nodes)

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
        UEdge(to=id, isSync = true, guard)
      }

      // save new node
      val newId = visited(key)
      newNodes.append((newId, UNode(name, actions, next)))
    }

    val nodes = newNodes.toIndexedSeq.sortBy(_._1).map(_._2)
    g.copy(nodes = nodes)
  }

  private type NodeKey = Set[Int]
  private type Guard = smt.BVExpr

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
          (smt.BVAnd(smt.BVNot(oldGuard), newEdge.guard), Set(newEdge.to)),
          (smt.BVAnd(oldGuard, smt.BVNot(newEdge.guard)), oldNext),
          (smt.BVAnd(oldGuard, newEdge.guard), oldNext ++ Set(newEdge.to)),
        )
        // simplify guards and filter out infeasible edges
          .map { case (guard, next) => (solver.simplify(guard), next) }
          .filter { case (guard, _) => solver.isSat(guard) }
      }

      // merge edges with same target
      val merged = feasible.groupBy(_._2).toList.map { case (next, guards) =>
        if(guards.size == 1) { guards.head } else {
          // either edge will take us to the same state:
          val combined = solver.simplify(guards.map(_._1).reduce(smt.BVOr(_, _)))
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
      val info = UGraphPass.mergeInfo(actions.map(_.info).toSet.toSeq)
      val guard = solver.simplify(actions.map(_.guard).reduce(smt.BVOr(_, _)))
      UAction(a, info, guard)
    }

    n.copy(actions = actions)
  }
}

object TagInternalNodes {
  def name: String = "TagInternalNodes"
  def run(g: UGraph, signal: String): UGraph = {
    val nodes = g.nodes.head +: g.nodes.drop(1).map(onNode(_, signal))
    g.copy(nodes = nodes)
  }
  private def onNode(n: UNode, signal: String): UNode = if(n.next.isEmpty) { n }  else {
    n.copy(actions = n.actions :+ UAction(ASignal(signal), ir.NoInfo))
  }
}

/** Expands the graph by  */
object DoFork {
  def name: String = "DoFork"
  def run(g: UGraph, entries: Map[Set[String], Int]): UGraph = {
    val nodes = g.nodes.map(onNode(_, entries))
    g.copy(nodes = nodes)
  }

  private def onNode(n : UNode, entries: Map[Set[String], Int]): UNode = {
    val signals = n.actions.collect { case UAction(ASignal(name), _ , guard) => (name, guard) }
    val forks = signals.filter(_._1 == "fork")
    if(forks.isEmpty) return n
    val forkGuards = forks.map(_._2).reduce(smt.BVOr(_, _))

    // we are over approximating here, assuming that all could be active at the same time
    val active = signals.map(_._1).filter(_.startsWith("A:")).map(_.drop(2)).toSet

    // check if we already know a state which we can fork to
    val to = entries.get(active) match {
      case Some(id) => id
      case None => throw new NotImplementedError(s"TODO: create new entry for ${active}")
    }

    // new edge
    val forkEdge = UEdge(to = to, isSync = false, forkGuards)

    // remove forks
    val nonForkActions = n.actions.filter{ case UAction(ASignal("fork"), _, _) => false case _ => true}

    n.copy(next = n.next :+ forkEdge, actions = nonForkActions)
  }

}