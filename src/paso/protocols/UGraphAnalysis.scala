// Copyright 2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.ir
import maltese.passes.Analysis
import maltese.smt
import scala.collection.mutable

/** Checks to ensure that a given UGraph can be collapsed into only synchronous edges.
 *  - Ensure that inputs are only modified if the output has not been read in the same cycle yet.
 *  - Ensure that either all paths to the final node fork, or none do.
 *  - Ensure that sticky input values do not depend on the path taken.
 */
class UGraphAnalysis(g: UGraph, protocolInfo: ProtocolInfo, combPaths: Seq[(String, Seq[String])]) {

  def run(): Unit = {
    // find all paths
    var visited = Set(0)
    val todo = mutable.Stack(0)
    while(todo.nonEmpty) {
      val id = todo.pop()
      val paths = findSingleStepPaths(id)

      val isFinalState = paths.isEmpty
      val newNext = paths.map(_.to).toSet.toSeq.filterNot(visited.contains)
      newNext.foreach(todo.push)
      visited ++= newNext.toSet
    }


    println(combPaths)
  }

  case class InputValue(name: String, value: smt.BVExpr, sticky: Boolean, info: ir.Info = ir.NoInfo)
  case class OutputRead(name: String, info: ir.Info = ir.NoInfo)
  private case class DataFlowInfo(mappings: Map[String, BigInt], hasForked: Boolean, stickyInputs: Map[String, InputValue])


  private case class Path(guard: List[smt.BVExpr], to: Int, actions: List[UAction] = List()) {
    actions.foreach(a => assert(a.guard.isEmpty))
  }


  // TODO: combine executing and exploring paths
  //       this is necessary since we want to analyze the when conditions
  //       to make sure that they do not depend on inputs that have not been set or
  //       arguments that have not been mapped yet.
  private def findSingleStepPaths(nodeId: Int, guard: List[smt.BVExpr] = List()): List[Path] = {
    val node = g.nodes(nodeId)
    val actions = node.actions.map(a => a.copy(guard = guard ++ a.guard))
    val next = node.next.flatMap {
      case UEdge(g, true, to) => List(Path(guard ++ g, to))
      case UEdge(g, false, to) => findSingleStepPaths(to, guard ++ g)
    }
    next.map(n => n.copy(actions = actions ++ n.actions))
  }

  /** Throws an exception if the actions are not allowed. Make sure to only check paths that might be feasible
   * to reduce false positives! */
  private def executePath(p: Path, in: DataFlowInfo): DataFlowInfo = {
    p.actions.foreach(a => assert(a.guard.isEmpty))
    val inputs = new mutable.HashMap() ++ in.stickyInputs
    val outputs = new mutable.HashMap[String, List[ir.Info]]()
    var hasForked = in.hasForked
    val signals = new mutable.HashMap[String, List[ir.Info]]()

    p.actions.foreach { case UAction(a, info, guard) =>
      a match {
        case ASignal(name) =>
          // remember that the signal was activated
          signals(name) = signals.getOrElse(name, List()) :+ info
        case ASet(input, rhs, isSticky) =>
        case AUnSet(input) =>
        case AAssert(cond) =>
        case AIOAccess(pin, bits) =>
          throw new RuntimeException(s"Unexpected io access statement from: ${info.serialize}")
        case _ : AMapping =>
          throw new RuntimeException(s"Unexpected mapping statement from: ${info.serialize}")
      }
     }
  }


  /** Reading a symbol has different restrictions depending on its kind:
   * - args: needs to be mapped before it is used as a rvalue (besides for sets, which actually do the mapping)
   * - rets: should only be used after dependent input args have been mapped (currently just allowed ... :( )
   * - inputs: (1) if already set: just return value (2) if not set: create new random input (not supported yet)
   * - outputs: output will be added to read outputs which are used to decide whether an input can be set
   */
  private def analyzeRValue(e: smt.BVExpr, getInput: smt.BVSymbol => Option[smt.BVExpr], isMapped: smt.BVSymbol => Boolean, info: ir.Info = ir.NoInfo, isSet: Boolean = false): (PathCtx, smt.BVExpr) = {
    val syms = Analysis.findSymbols(e).map(_.asInstanceOf[smt.BVSymbol])
    val args = syms.filter(s => protocolInfo.args.contains(s.name))
    val rets = syms.filter(s => protocolInfo.rets.contains(s.name))
    val inputs = syms.filter(s => protocolInfo.inputs.contains(s.name))
    val outputs = syms.filter(s => protocolInfo.outputs.contains(s.name))
    val unknown = syms.toSet -- (args ++ rets ++ inputs ++ outputs).toSet
    if(unknown.nonEmpty) {
      throw new RuntimeException(s"Unknown symbol $unknown in $e ${info.serialize}")
    }

    // args
    if(!isSet) { // set maps any unmapped args
      args.foreach { arg =>
        assert(isMapped(arg), s"Argument $arg needs to first be bound to an input before reading it!${info.serialize}")
      }
    }

    // inputs
    val inputReplacements = inputs.map { i => i.name ->
      getInput(i).getOrElse(throw new RuntimeException(s"Input $i cannot be read before it is set!${info.serialize}"))
    }.toMap

    // record which outputs where read
    val outputsRead = outputs.map(o => o.name -> OutputRead(o.name, info))

    val newExpr = replaceSymbols(e, inputReplacements).asInstanceOf[smt.BVExpr]
  }

  private def replaceSymbols(e: smt.SMTExpr, subs: Map[String, smt.SMTExpr]): smt.SMTExpr = e match {
    case s : smt.BVSymbol => subs.getOrElse(s.name, s)
    case other => other.mapExpr(replaceSymbols(_, subs))
  }
}
