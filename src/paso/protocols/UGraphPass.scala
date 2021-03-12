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
      if(n.next.isEmpty || outgoingEdgeAssumption == smt.True()) List()
      else destructAnd(outgoingEdgeAssumption).map(cond => UAction(AAssume(cond), ir.NoInfo))

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

    val nodes = noForwarding.nodes.zipWithIndex.map { case (n, id) => onNode(g, n, id) }
    // removing all asynchronous edges might leave some nodes unreachable
    RemoveUnreachable.run(noForwarding.copy(nodes = nodes))
  }

  private def onNode(g: UGraph, n: UNode, nid: Int): UNode = {
    // early exit
    if(n.next.forall(_.isSync)) return n

    // find all single step paths
    val paths = findSingleStepPaths(g, smt.True(), n, List(nid))
    val next = paths.map(p => UEdge(to = p.to, isSync = true, p.guard))
    val actions = paths.flatMap(_.actions)

    // println(s"#$nid [${n.name}] paths: ${paths.size}, actions: ${actions.size}, old actions: ${n.actions.size}")

    // ensure that there are no actions that depend on a fixed order
    actions.map(_.a).foreach {
      case _: ASet | _: AUnSet =>
        throw new RuntimeException(s"UnSet/Set commands are not supported in this pass! ${n}")
      case _ =>
    }

    n.copy(actions = actions, next = next)
  }

  private case class Path(actions: List[UAction], guard: smt.BVExpr, to: Int)
  private def findSingleStepPaths(g: UGraph, guard: smt.BVExpr, from: UNode, visited: List[Int]): List[Path] = {
    val paths = from.next.flatMap { n =>
      if(n.isSync) {
        List(Path(List(), smt.BVAnd(guard, n.guard), n.to))
      } else {
        assert(!visited.contains(n.to), f"Found a cycle without a synchronous edge: ${(visited :+ n.to).mkString(" -> ")}")
        findSingleStepPaths(g, smt.BVAnd(guard, n.guard), g.nodes(n.to), visited :+ n.to)
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

/** Removes all states that have:
 *  - no actions
 *  - no outgoing edges
 * */
object RemoveEmptyLeafStates extends UGraphPass {
  override def name: String = "RemoveEmptyLeafStates"
  override def run(g: UGraph): UGraph = {
    val remove = getAllEmptyLeaves(g.nodes)
    if(remove.isEmpty) { g } else {
      val removedEdges = g.copy(nodes = g.nodes.map(removeEdges(_, remove)))
      RemoveUnreachable.run(removedEdges)
    }
  }

  private def getAllEmptyLeaves(nodes: IndexedSeq[UNode]): Set[Int] = {
    var remove = Set[Int]()
    var done = false
    while(!done) {
      val remaining = nodes.zipWithIndex.filterNot{ case (_, i) => remove(i) }
      val newRemove = remaining.filter { case (n, _) => isEmptyLeaf(n, remove) }.map(_._2).toSet
      done = newRemove.isEmpty
      remove ++= newRemove
    }
    remove
  }

  private def isEmptyLeaf(n: UNode, removed: Set[Int]): Boolean = {
    val noNext = n.next.forall(e => removed(e.to))
    noNext && n.actions.isEmpty
  }

  private def removeEdges(e: UNode, removed: Set[Int]): UNode = {
    val next = e.next.filterNot(n => removed(n.to))
    e.copy(next = next)
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
      val name = nodes.map(_.name).filterNot(_.isEmpty).mkString(" and ")

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
      val finalGuards = finalEdges.map(_._1)

      // we only take the new edge iff the new edge guard and no other guards are true
      val onlyNewEdge = (smt.BVAnd(finalGuards.map(smt.BVNot) :+ newEdge.guard), Set(newEdge.to))

      // we take only the old edges iff the old ege guard and not the new edge guard is true
      val onlyOldEdge = finalEdges.map { case (g, n) => (smt.BVAnd(g, smt.BVNot(newEdge.guard)), n) }

      // we take the combination of an old edge and the new edge, when both are true and all other old edges are false
      // note: that we cannot take more than one old edge at a time since we maintain the invariant that all
      //       "finalEdges" are mutually exclusive

      val combinedEdges = finalEdges.zipWithIndex.map { case ((g, n), ii) =>
        val guard: List[smt.BVExpr] =
          finalGuards.take(ii).map(smt.BVNot) ++ List(g) ++ finalGuards.drop(ii + 1).map(smt.BVNot) ++ List(newEdge.guard)
        (smt.BVAnd(guard), Set(newEdge.to) ++ n)
      }

      val feasible = (onlyNewEdge +: onlyOldEdge ++: combinedEdges)
        // simplify guards and filter out infeasible edges
          .map { case (guard, next) => (solver.simplify(guard), next) }
          .filter { case (guard, _) => solver.isSat(guard) }

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
class MergeActionsAndEdges(solver: GuardSolver) extends UGraphPass {
  override def name: String = "MergeActions"
  override def run(g: UGraph): UGraph = {
    val nodes = g.nodes.map(onNode)
    g.copy(nodes = nodes)
  }

  private def onNode(n: UNode): UNode = {
    val byAction = n.actions.groupBy(_.a).toList
    val byToAndSync = n.next.groupBy(e => (e.to, e.isSync)).toList

    // exit early if there are no actions or edges that can be merged
    if(byAction.size == n.actions.size && byToAndSync.size == n.next.size) return n

    val actions = byAction.map { case (a, actions) =>
      val info = UGraphPass.mergeInfo(actions.map(_.info).toSet.toSeq)
      val guard = solver.simplify(actions.map(_.guard).reduce(smt.BVOr(_, _)))
      UAction(a, info, guard)
    }

    val next = byToAndSync.map { case ((to, isSync), edges) =>
      val guard = solver.simplify(edges.map(_.guard).reduce(smt.BVOr(_, _)))
      UEdge(to, isSync, guard)
    }

    n.copy(actions = actions, next = next)
  }
}

class TagInternalNodes(signal: String) extends UGraphPass {
  override def name: String = "TagInternalNodes"
  override def run(g: UGraph): UGraph = {
    val nodes = g.nodes.head +: g.nodes.drop(1).map(onNode)
    g.copy(nodes = nodes)
  }
  private def onNode(n: UNode): UNode = if(n.next.isEmpty) { n }  else {
    n.copy(actions = n.actions :+ UAction(ASignal(signal), ir.NoInfo))
  }
}

class Replace(signals: Map[String, String] = Map(), symbols: Map[String, smt.BVExpr] = Map()) extends UGraphPass {
  override def name = "ReplacePass"
  override def run(g: UGraph): UGraph = {
    if(signals.isEmpty && symbols.isEmpty) return g
    val nodes = g.nodes.map(onNode)
    g.copy(nodes = nodes)
  }
  private def onNode(n: UNode): UNode = {
    val actions = n.actions.map { action =>
      val a = action.a match {
        case ASignal(name) => ASignal(signals.getOrElse(name, name))
        case AAssert(cond) => AAssert(replace(cond))
        case AAssume(cond) => AAssume(replace(cond))
        case AMapping(arg, hi, lo, update) => AMapping(replace(arg).asInstanceOf[smt.BVSymbol], hi, lo, replace(update))
        case i : AInputAssign => i
        case other => throw new RuntimeException(s"Unexpected action $other")
      }
      action.copy(a = a)
    }
    n.copy(actions = actions)
  }
  private def replace(e: smt.BVExpr): smt.BVExpr = replaceSMT(e).asInstanceOf[smt.BVExpr]
  private def replaceSMT(e: smt.SMTExpr): smt.SMTExpr = e match {
    case s : smt.BVSymbol => symbols.getOrElse(s.name, s)
    case other => other.mapExpr(replaceSMT)
  }
}

class PrefixSignals(prefix: String, ignoreSignals: Set[String] = Set()) extends UGraphPass {
  override def name = "PrefixSignals"
  override def run(g: UGraph): UGraph = g.copy(nodes = g.nodes.map(onNode))
  private def onNode(n: UNode): UNode = n.copy(actions = n.actions.map(onAction))
  private def onAction(a: UAction): UAction = a.a match {
    case ASignal(name) if !ignoreSignals(name) =>
      a.copy(a = ASignal(prefix + name))
    case _ => a
  }
}

class RemoveSignalsEndingWith(suffixes: List[String]) extends UGraphPass {
  override def name = "RemoveSignalsEndingWith"
  override def run(g: UGraph): UGraph = g.copy(nodes = g.nodes.map(onNode))
  private def onNode(n: UNode): UNode = n.copy(actions = n.actions.flatMap(onAction))
  private def onAction(a: UAction): Option[UAction] = a.a match {
    case ASignal(name) =>
      val doRemove = suffixes.exists(s => name.endsWith(s))
      if(doRemove) None else Some(a)
    case _ => Some(a)
  }
}

/** Expands the graph by  */
class ExpandForksPass(protos: Seq[ProtocolInfo], solver: GuardSolver, graphDir: String = "") extends UGraphPass {
  override def name: String = "ExpandForksPass"

  private val startPoints = mutable.HashMap[Seq[(String,Int)], Int]()
  private val todo = mutable.Stack[(Seq[(String,Int)], Int)]()
  private var graphSize: Int = 0
  private var maxId : Int = 0

  private val toDFA = Seq(RemoveAsynchronousEdges, new MakeDeterministic(solver), new MergeActionsAndEdges(solver))

  override def run(merged: UGraph): UGraph = {
    // we start with no active transactions
    startPoints.clear()
    startPoints(activeToStart(Set())) = 0
    todo.clear()
    todo.push((activeToStart(Set()), 0))
    graphSize = merged.size
    maxId = merged.size - 1

    var graph = UGraph(merged.name, IndexedSeq())
    var count = 0
    while(todo.nonEmpty) {
      // add copies of the merged protocols for every new starting point
      val withStarts = addNewStarts(merged, graph)
      // turn into a DFA so that we know exactly which protocols are active at the fork points
      val noAsyncEdges = toDFA(2).run(toDFA(0).run(withStarts))
      val deterministic = toDFA(1).run(noAsyncEdges)
      val dfa = toDFA(2).run(deterministic)
      //val dfa = toDFA.foldLeft(withStarts)((in, pass) => pass.run(in))
      // scan for new forks
      maxId = dfa.size - 1
      val resolvedFork = UGraph(dfa.name, dfa.nodes.map(onNode))
      // this is out new graph
      graph = resolvedFork

      //
      plot(withStarts, s"A_with_starts", count)
      plot(noAsyncEdges, s"B_no_async", count)
      plot(deterministic, s"C_dfa", count)
      plot(dfa, s"D_dfa_simple", count)
      plot(resolvedFork, s"E_resolved_fork.dot", count)
      count += 1
    }

    val noAsyncEdges = toDFA(2).run(toDFA(0).run(graph))
    val deterministic = toDFA(1).run(noAsyncEdges)
    val dfa = toDFA(2).run(deterministic)
    plot(noAsyncEdges, s"B_no_async", count)
    plot(deterministic, s"C_dfa", count)
    plot(dfa, s"D_dfa_simple", count)

    dfa
  }

  private def plot(g: UGraph, name: String, count: Int): Unit = if(graphDir.nonEmpty) {
    val filename = s"$graphDir/fork_${count}_$name.dot"
    ProtocolVisualization.saveDot(g, false, filename)
  }

  private def addNewStarts(merged: UGraph, graph: UGraph): UGraph = {
    var nodes = graph.nodes
    val smallerToLargerId = todo.toList.sortBy(_._2)
    smallerToLargerId.foreach { case (active, id) =>
      assert(id == nodes.size, s"$smallerToLargerId")
      nodes = nodes ++ replaceProtocolInstances(merged, active, id)
    }
    todo.clear()
    UGraph(merged.name, nodes)
  }

  private def signalNames = List("Active", "Commit", "AllMapped")
  private def replaceProtocolInstances(merged: UGraph, newIds: Seq[(String, Int)], shift: Int): IndexedSeq[UNode] = {
    // replace symbols and signals for all new instances
    val replacements = newIds.zip(protos).map { case ((n, id), p) =>
      assert(n == p.name)
      val replaceSignal = if(id == 0) List() else {
        signalNames.map(s => s"${p.name}$$0_$s" -> s"${p.name}$$${id}_$s")
      }
      val replaceSyms = if(id == 0) List() else {
        val suffix = "$" + id
        p.args.flatMap { case(name, width) =>
          List(name -> smt.BVSymbol(name + suffix, width), (name + "$prev") -> smt.BVSymbol(name + suffix + "$prev", width))
        } ++ p.rets.map{ case (name, width) => name -> smt.BVSymbol(name + suffix, width) }
      }
      (replaceSignal, replaceSyms)
    }
    val signals = replacements.flatMap(_._1).toMap
    val syms = replacements.flatMap(_._2).toMap
    val replaced = new Replace(signals, syms).run(merged)

    // shift edge targets since we are appending the nodes
    val shifted = replaced.nodes.map { n =>
      val next = n.next.map(n => n.copy(to = n.to + shift))
      n.copy(next=next)
    }
    shifted
  }


  private def getStart(key: Seq[(String, Int)]): Int = {
      startPoints.get(key) match {
      case Some(id: Int) => id
      case None =>
        // calculate the id of a new node
        val id = maxId + 1
        maxId += graphSize
        // add new entry
        startPoints(key) = id
        todo.push((key, id))
        id
    }
  }

  /** calculates which protocol instances should be started depending on the current active states */
  private def activeToStart(active: Set[String]): Seq[(String, Int)] = {
    // TODO: maybe add caching
    // first we find a non-active instance for every protocol
    val activeInstances = getActiveInstances(active)
    protos.map { p =>
      val iActive = activeInstances.getOrElse(p.name, Set())
      // select the lowest available id
      val id = Iterator.from(0).find(i => !iActive(i)).get
      p.name -> id
    }
  }

  private def getActiveInstances(active: Set[String]): Map[String, Set[Int]] =
    active.groupBy(_.split('$').head).mapValues(_.map(_.split('$').last.toInt))

  private def onNode(n : UNode): UNode = {
    val signals = n.actions.collect { case UAction(ASignal(name), _ , guard) => (name, guard) }
    val forks = signals.filter(_._1 == "fork")
    if(forks.isEmpty) return n
    val forkGuards = forks.map(_._2).reduce(smt.BVOr(_, _))

    // we are over approximating here, assuming that all could be active at the same time
    val active = signals.map(_._1).filter(_.endsWith("_Active")).map(_.dropRight(7)).toSet

    // check if we already know a state which we can fork to
    val to = getStart(activeToStart(active))

    // new edge
    val forkEdge = UEdge(to = to, isSync = false, forkGuards)

    // remove forks
    val nonForkActions = n.actions.filter{ case UAction(ASignal("fork"), _, _) => false case _ => true}

    n.copy(next = n.next :+ forkEdge, actions = nonForkActions)
  }
}


/** Takes in the output of [[ProtocolToSyncUGraph]] and adds
 *  a "Commit" signals for states in which the protocol needs to commit.
 *  It also checks whether:
 *  - the protocol accesses any return arguments after it has committed
 *  - the protocol maps all inputs before committing
 *  These properties are helpful in deciding how to attach the functional model
 *  to the protocol graph.
 */
class CommitAnalysis(rets: Map[String, Int]) {
  def name = "CommitAnalysis"

  case class Result(readAfterCommit: Boolean, mapInputsBeforeCommit: Boolean)

  def run(g: UGraph): (UGraph, Result) = {
    val (result, commits) = analyze(g)
    assert(commits.nonEmpty, "Found no commits!")

    // add commit signals
    val nodes = g.nodes.zipWithIndex.map { case (n, id) => commits.get(id) match {
      case Some(guard) =>
        val a = UAction(ASignal("Commit"), ir.NoInfo, guard)
        n.copy(actions = a +: n.actions)
      case None => n
    }}

    (g.copy(nodes=nodes), result)
  }

  private def analyze(g: UGraph): (Result, Map[Int, smt.BVExpr]) = {
    // we initially assume that we do not read after a commit
    var readAfterCommit = false
    // we initially assume that we will map all inputs before committing
    var mapInputsBeforeCommit = true

    val visited = mutable.HashSet[Int]()
    val todo = mutable.Stack[(Int, Boolean)]()
    val commits = mutable.HashMap[Int, smt.BVExpr]()

    visited.add(0)
    todo.push((0, false))

    while(todo.nonEmpty) {
      val (nid, hasCommitted) = todo.pop()
      val node = g.nodes(nid)

      // check conditions
      if(hasCommitted && readsRets(node)) {
        readAfterCommit = true
      }
      if(hasCommitted && mapsAll(node)) {
        mapInputsBeforeCommit = false
      }

      // we want to assume that forks do not have non-trivial guards
      // this is reasonable since they always happen directly after a step
      getForks(node).foreach(a => assert(a.guard == smt.True(), s"$a"))

      // check to see if this node commits (and under which conditions)
      val next = node.next.map(n => (n.guard, g.nodes(n.to)))
      val nextForks = next.flatMap{ case (g, n) => if(getForks(n).nonEmpty) Some(g) else None }
      if(nextForks.nonEmpty) {
        commits(nid) = smt.BVOr(nextForks)
      }

      node.next.map(_.to).filterNot(visited).foreach { id =>
        visited.add(id)
        // a node will have committed if we committed previously or if it forks
        val com = hasCommitted || getForks(g.nodes(id)).nonEmpty
        todo.push((id, com))
      }
    }

    (Result(readAfterCommit, mapInputsBeforeCommit), commits.toMap)
  }

  private def getForks(n: UNode): List[UAction] = {
    n.actions.collect { case a @ UAction(ASignal("fork"), _, _) => a }
  }

  private def mapsAll(n: UNode): Boolean = {
    n.actions.collect { case a @ UAction(ASignal("AllMapped"), _, guard) =>
      assert(guard == smt.True(), s"AllMapped signal has non-trivial guard: $guard")
      a
    }.nonEmpty
  }

  private def readsRets(n: UNode): Boolean = n.actions.exists(readsRets)
  private def readsRets(a: UAction): Boolean = readExprs(a).exists(readsRets)
  private def readExprs(a: UAction): Iterable[smt.BVExpr] = List(a.guard) ++ (a.a match {
    case ASet(_, rhs, _) => List(rhs)
    case AAssert(cond) => List(cond)
    case AAssume(cond) => List(cond)
    case _ => List()
  })
  private def readsRets(e: smt.SMTExpr): Boolean = e match {
    case smt.BVSymbol(name, _) if rets.contains(name) => true
    case other if other.children.isEmpty => false
    case other => other.children.exists(readsRets)
  }
}