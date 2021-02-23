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
class ProtocolToSyncUGraph(solver: smt.Solver, g: UGraph, protocolInfo: ProtocolInfo, combPaths: Seq[(String, Seq[String])]) {

  private val guardSolver = new GuardSolver(solver)
  private def isFeasible(ctx: PathCtx): Boolean = guardSolver.isSat(ctx.guard)

  private def fixPrefix(name: String): String = {
    assert(name.startsWith("io"))
    protocolInfo.ioPrefix + name.drop(2)
  }
  private val inputToOutputs: Map[String, Seq[String]] = combPaths
    .flatMap{ case (sink, sources) => sources.map(s => s -> sink)}
    .groupBy(_._1).map{ case (source, lst) => fixPrefix(source) -> lst.map(_._2).map(fixPrefix) }
    .toMap

  def run(): UGraph = {
    // collect new nodes
    val newNodes = mutable.ArrayBuffer[(Int, UNode)]()
    val nodeIds = mutable.HashMap[(Int, DataFlowInfo), Int]()

    // find all paths
    val startMappings = protocolInfo.args.keys.map(_ -> BigInt(0)).toMap
    val start = (0, DataFlowInfo(startMappings, false, Seq()))
    nodeIds(start) = 0
    var visited = Set(start)
    val todo = mutable.Stack(start)
    while(todo.nonEmpty) {
      val (id, flow) = todo.pop()
      val paths = executeSingleStepPath(id, flowToPathCtx(flow))

      val newNext = paths.map(p => (p.to, p.flowOut)).toSet.toSeq.filterNot(visited.contains)
      newNext.foreach { n =>
        todo.push(n)
        nodeIds(n) = nodeIds.size
      }
      visited ++= newNext.toSet

      val newId = nodeIds((id, flow))
      newNodes.append((newId, pathsToNode(flow, paths, nodeIds)))
    }

    val nodes = newNodes.sortBy(_._1).map(_._2).toIndexedSeq
    UGraph(g.name, nodes)
  }

  private def pathsToNode(flowIn: DataFlowInfo, paths: List[Path], getId: ((Int, DataFlowInfo)) => Int): UNode = {
    val actions = paths.flatMap(p => p.actions.map(a => a.copy(guard = p.guard)))
    val next = paths.map(p => UEdge(to = getId((p.to, p.flowOut)), isSync = true, p.guard))

    // if this is a final state and we have not forked yet => implicit fork
    val isFinal = next.isEmpty
    val hasForked = flowIn.hasForked || actions.collectFirst{ case UAction(ASignal("fork"), _, _) => true }.getOrElse(false)
    val forkAction = if(isFinal && !hasForked) Some(UAction(ASignal("fork"), ir.NoInfo)) else None

    val name = "" // TODO
    UNode(name, actions ++ forkAction, next)
  }

  private def executeSingleStepPath(nodeId: Int, ctx: PathCtx): List[Path] = {
    val node = g.nodes(nodeId)

    // in this form actions should not have guards!
    node.actions.foreach(a => assert(a.guard == smt.True()))

    // execute actions in sequence
    val afterActions = node.actions.foldLeft(ctx)((ctx, a) => execute(ctx, a))

    // iterate over out going edges
    node.next.flatMap { case UEdge(to, isSync, g) =>
      val (guardReads, guard) = analyzeRValue(g, afterActions)
      val ctxWithGuard = afterActions.addRead(guardReads).addGuard(guard)
      if(isFeasible(ctxWithGuard)) {
        if (isSync) {
          List(finishPath(to, ctxWithGuard))
        } else {
          executeSingleStepPath(to, ctxWithGuard)
        }
      } else {
        // if the edge is infeasible, we ignore it
        List()
      }
    }
  }

  // Path Execution
  private case class InputValue(name: String, value: smt.BVExpr, sticky: Boolean, info: ir.Info = ir.NoInfo)
  private case class OutputRead(name: String, info: ir.Info = ir.NoInfo)
  private case class DataFlowInfo(mappings: Map[String, BigInt], hasForked: Boolean, stickyInputs: Seq[(String, InputValue)])

  /** execution context of a single path */
  private case class PathCtx(
    prevMappings: Map[String, BigInt], hasForked: Boolean, inputs: Map[String, InputValue],
    guard: smt.BVExpr, signals: Map[String, List[ir.Info]], asserts: List[(AAssert, ir.Info)],
    outputsRead: Map[String, List[OutputRead]]
  ) {
    /** list of current mappings which takes current input values into account */
    def mappedArgs: Map[String, BigInt] = {
      val updates =
        inputs.flatMap{ case (_, v) => BitMapping.mappedBits(v.value) }
          .filter{ case (name, _) => prevMappings.contains(name) }
      updates.foldLeft(prevMappings){ case (map, (name, bits)) => map + (name -> (map.getOrElse(name, BigInt(0)) | bits)) }
    }
    def addGuard(g: smt.BVExpr): PathCtx = copy(guard = smt.BVAnd(guard, g))
    def addRead(read: Iterable[OutputRead]): PathCtx = if(read.isEmpty) this else {
      val combined = mutable.HashMap[String, List[OutputRead]]()
      read.foreach { r =>
        val prev = combined.getOrElse(r.name, outputsRead.getOrElse(r.name, List()))
        combined(r.name) = prev :+ r
      }
      copy(outputsRead = outputsRead ++ combined)
    }
    def addAssert(a: AAssert, i: ir.Info): PathCtx = copy(asserts = asserts :+ (a,i))
    def setSignal(name: String, info: ir.Info): PathCtx =
      copy(signals = signals ++ Map(name -> (signals.getOrElse(name, List()) :+ info)))
    def setInput(v: InputValue): PathCtx = copy(inputs = inputs ++ Map(v.name -> v))
    def clearInput(name: String): PathCtx = copy(inputs = inputs -- Set(name))
    def isMapped(arg: smt.BVSymbol): Boolean = mappedArgs.contains(arg.name)
    def getInput(input: smt.BVSymbol): Option[smt.BVExpr] = inputs.get(input.name).map(_.value)
  }

  private def flowToPathCtx(flow: DataFlowInfo): PathCtx = PathCtx(
    flow.mappings, flow.hasForked, flow.stickyInputs.toMap,
    smt.True(), Map(), List(), Map()
  )

  private def pathCtxToFlow(ctx: PathCtx): DataFlowInfo = DataFlowInfo(
    ctx.mappedArgs, ctx.hasForked || ctx.signals.contains("fork"), ctx.inputs.filter(_._2.sticky).toSeq.sortBy(_._1)
  )

  private case class Path(guard: smt.BVExpr, to: Int, flowOut: DataFlowInfo, actions: List[UAction] = List()) {
    actions.foreach(a => assert(a.guard == smt.True()))
  }

  private def finishPath(to: Int, ctx: PathCtx): Path = {
    val asserts = ctx.asserts.map{ case (a,i) => UAction(a, i) }
    val inputs = processInputAssignments(ctx.prevMappings, ctx.inputs.values)

    val signals = ctx.signals.map{ case (name, infos) =>
      val info = if(infos.length > 1) ir.MultiInfo(infos) else infos.head
      UAction(ASignal(name), info)
    }
    val flowInfo = pathCtxToFlow(ctx)
    Path(ctx.guard, to, flowInfo, inputs ++ signals ++ asserts)
  }

  /** process final input state into assumes, mappings and markers for the inputs that were assigned */
  private def processInputAssignments(prevMappings: Map[String, BigInt], inputs: Iterable[InputValue]): List[UAction] = {
    val assignments = inputs.toList.sortBy(_.name)
    val inputsAssigned = assignments.map(v => UAction(AInputAssign(v.name), v.info))
    val sets = assignments.map(i => UAction(ASet(i.name, i.value, i.sticky), i.info))

    // we separate mappings from assumptions
    var mappings = prevMappings
    val mapsAndConstraints = assignments.flatMap { v =>
      val (constr, maps, updatedMappings) = BitMapping.analyze(mappings, smt.BVSymbol(v.name, v.value.width), v.value)
      mappings = updatedMappings
      constr.map(simplify).map(c => UAction(AAssume(c), v.info)) ++
        maps.map(simplify).map(m => UAction(exprToMapping(m.asInstanceOf[smt.BVEqual]), v.info))
    }

    // TODO: do we need to track input assignments or not?
    //inputsAssigned
    mapsAndConstraints
  }

  private def exprToMapping(eq: smt.BVEqual): AMapping = {
    val input = eq.a
    val (arg, hi, lo) = eq.b match {
      case s : smt.BVSymbol => (s, s.width-1, 0)
      case smt.BVSlice(s: smt.BVSymbol, hi, lo) => (s, hi, lo)
      case other => throw new RuntimeException(s"Unexpected argument mapping expr: $other")
    }

    // if not the whole arg is update at once, we need to retain some of the previous state
    val prev = arg.rename(arg.name + "$prev")
    val leftPad = if(hi == arg.width - 1) { input }
    else { smt.BVConcat(smt.BVSlice(prev, arg.width-1, hi + 1), input) }
    val rightPad = if(lo == 0) { leftPad }
    else { smt.BVConcat(leftPad, smt.BVSlice(prev, lo-1, 0)) }

    AMapping(arg=arg, hi=hi, lo=lo, rightPad)
  }

  private def execute(ctx: PathCtx, action: UAction): PathCtx = action.a match {
    case ASignal(name) =>
      // remember that the signal was activated
      ctx.setSignal(name, action.info)
    case ASet(input, rhs, isSticky) =>
      // check that the input can still be set
      val sinks = inputToOutputs.getOrElse(input, List())
      sinks.foreach { sink =>
        if(ctx.outputsRead.contains(sink)) {
          val infos = ctx.outputsRead(sink).map(_.info.serialize).mkString(", ")
          throw new RuntimeException(s"Cannot set input $input ${action.info.serialize}!\n" +
          s"The output $sink has been read already in the same cycle: $infos")
        }
      }
      // apply the new value to the input
      val (reads, expr) = analyzeRValue(rhs, ctx, action.info, isSet = true)
      ctx.addRead(reads).setInput(InputValue(input, expr, isSticky, action.info))
    case AUnSet(input) =>
      ctx.clearInput(input)
    case AAssert(cond) =>
      val (reads, expr) = analyzeRValue(cond, ctx, action.info, isSet = false)
      ctx.addRead(reads).addAssert(AAssert(expr), action.info)
    case _ : AInputAssign =>
      throw new RuntimeException(s"Unexpected io access statement from: ${action.info.serialize}")
    case _ : AMapping =>
      throw new RuntimeException(s"Unexpected mapping statement from: ${action.info.serialize}")
  }

  /** Reading a symbol has different restrictions depending on its kind:
   * - args: needs to be mapped before it is used as a rvalue (besides for sets, which actually do the mapping)
   * - rets: should only be used after dependent input args have been mapped (currently just allowed ... :( )
   * - inputs: (1) if already set: just return value (2) if not set: create new random input (not supported yet)
   * - outputs: output will be added to read outputs which are used to decide whether an input can be set
   */
  private def analyzeRValue(e: smt.BVExpr, ctx: PathCtx, info: ir.Info = ir.NoInfo, isSet: Boolean = false): (Seq[OutputRead], smt.BVExpr) = {
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
        assert(ctx.isMapped(arg), s"Argument $arg needs to first be bound to an input before reading it!${info.serialize}")
      }
    }

    // inputs
    val inputReplacements = inputs.map { i => i.name ->
      ctx.getInput(i).getOrElse(throw new RuntimeException(s"Input $i cannot be read before it is set!${info.serialize}"))
    }.toMap

    // record which outputs where read
    val outputsRead = outputs
      // .filterNot(o => ctx.outputsRead.contains(o.name))
      .map(o => OutputRead(o.name, info))

    val newExpr = replaceSymbols(e, inputReplacements).asInstanceOf[smt.BVExpr]

    (outputsRead, newExpr)
  }

  private def analyzeRValue(es: List[smt.BVExpr], ctx: PathCtx): (List[OutputRead], List[smt.BVExpr]) = {
    var read = mutable.ListBuffer[OutputRead]()
    val out = es.map { e =>
      val (r, out) = analyzeRValue(e, ctx)
      read ++= r
      out
    }
    (read.toList, out)
  }

  private def replaceSymbols(e: smt.SMTExpr, subs: Map[String, smt.SMTExpr]): smt.SMTExpr = e match {
    case s : smt.BVSymbol => subs.getOrElse(s.name, s)
    case other => other.mapExpr(replaceSymbols(_, subs))
  }

  private def simplify(e: smt.BVExpr): smt.BVExpr =
    smt.SMTSimplifier.simplify(e).asInstanceOf[smt.BVExpr]
}
