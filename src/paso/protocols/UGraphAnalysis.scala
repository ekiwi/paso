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

  private def fixPrefix(name: String): String = {
    assert(name.startsWith("io"))
    protocolInfo.ioPrefix + name.drop(2)
  }
  private val inputToOutputs: Map[String, Seq[String]] = combPaths
    .flatMap{ case (sink, sources) => sources.map(s => s -> sink)}
    .groupBy(_._1).map{ case (source, lst) => fixPrefix(source) -> lst.map(_._2).map(fixPrefix) }
    .toMap

  def run(): Unit = {
    // find all paths
    val startFlow = DataFlowInfo(Map(), false, Seq())
    var visited = Set((0, startFlow))
    val todo = mutable.Stack((0, startFlow))
    while(todo.nonEmpty) {
      val (id, flow) = todo.pop()
      val paths = executeSingleStepPath(id, flowToPathCtx(flow))

      val isFinalState = paths.isEmpty
      val newNext = paths.map(p => (p.to, p.flowOut)).toSet.toSeq.filterNot(visited.contains)
      newNext.foreach(todo.push)
      visited ++= newNext.toSet
    }
  }


  private def executeSingleStepPath(nodeId: Int, ctx: PathCtx): List[Path] = {
    val node = g.nodes(nodeId)

    // in this form actions should not have guards!
    node.actions.foreach(a => assert(a.guard.isEmpty))

    // execute actions in sequence
    val afterActions = node.actions.foldLeft(ctx)((ctx, a) => execute(ctx, a))

    // iterate over out going edges
    node.next.flatMap { case UEdge(g, isSync, to) =>
      val (guardReads, guard) = analyzeRValue(g, afterActions)
      // TODO: check combined guard to ensure that it is feasible!
      val ctxWithGuard = afterActions.addRead(guardReads).addGuard(guard)
      if(isSync) { List(finishPath(to, ctxWithGuard))
      } else { executeSingleStepPath(to, ctxWithGuard)
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
    guard: List[smt.BVExpr], signals: Map[String, List[ir.Info]], asserts: List[(AAssert, ir.Info)],
    outputsRead: Map[String, List[OutputRead]]
  ) {
    /** list of current mappings which takes current input values into account */
    def mappedArgs: Map[String, BigInt] = {
      val updates =
        inputs.flatMap{ case (_, v) => BitMapping.mappedBits(v.value) }
          .filter{ case (name, _) => prevMappings.contains(name) }
      updates.foldLeft(prevMappings){ case (map, (name, bits)) => map + (name -> (map.getOrElse(name, BigInt(0)) | bits)) }
    }
    def addGuard(g: List[smt.BVExpr]): PathCtx = copy(guard = guard ++ g)
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
    List(), Map(), List(), Map()
  )

  private def pathCtxToFlow(ctx: PathCtx): DataFlowInfo = DataFlowInfo(
    ctx.mappedArgs, ctx.hasForked, ctx.inputs.filter(_._2.sticky).toSeq.sortBy(_._1)
  )

  private case class Path(guard: List[smt.BVExpr], to: Int, flowOut: DataFlowInfo, actions: List[UAction] = List()) {
    actions.foreach(a => assert(a.guard.isEmpty))
  }

  private def finishPath(to: Int, ctx: PathCtx): Path = {
    val asserts = ctx.asserts.map{ case (a,i) => UAction(a, i) }
    val sets = ctx.inputs.values.toSeq.sortBy(_.name).map(i => UAction(ASet(i.name, i.value, i.sticky), i.info)).toList
    val signals = ctx.signals.map{ case (name, infos) =>
      val info = if(infos.length > 1) ir.MultiInfo(infos) else infos.head
      UAction(ASignal(name), info)
    }
    val flowInfo = pathCtxToFlow(ctx)
    Path(ctx.guard, to, flowInfo, sets ++ signals ++ asserts)
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
      assert(cond.length == 1)
      val (reads, expr) = analyzeRValue(cond.head, ctx, action.info, isSet = false)
      ctx.addRead(reads).addAssert(AAssert(List(expr)), action.info)
    case _ : AIOAccess =>
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
}
