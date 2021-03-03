// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols.old

import firrtl.backends.experimental.smt.ExpressionConverter
import firrtl.ir
import maltese.passes.Analysis
import maltese.smt
import maltese.smt.solvers.Solver
import paso.protocols._

import scala.collection.mutable

case class InputValue(name: String, value: smt.BVExpr, sticky: Boolean, info: ir.Info = ir.NoInfo)
case class OutputRead(name: String, info: ir.Info = ir.NoInfo)

case class PathCtx(
  cond: List[smt.BVExpr], prevMappings: Map[String, BigInt], hasForked: Boolean,
  asserts: List[smt.BVExpr],
  inputValues: Map[String, InputValue], outputsRead: Map[String, OutputRead],
  next: Option[String]
) {
  def mappedArgs: Map[String, BigInt] = {
    val updates =
      inputValues.flatMap{ case (_, v) => BitMapping.mappedBits(v.value) }
        .filter{ case (name, _) => prevMappings.contains(name) }
    updates.foldLeft(prevMappings){ case (map, (name, bits)) => map + (name -> (map.getOrElse(name, BigInt(0)) | bits)) }
  }
}

case class ProtocolPaths(info: ProtocolInfo, steps: Seq[(String, List[PathCtx])])

private case class Mapping(prevSteps: List[String], map: Map[String, BigInt])
private case class DataFlowInfo(prevSteps: List[String], prevMappings: Map[String, BigInt], hasForked: Boolean, stickyInputs: Map[String, InputValue])

/** Encodes imperative protocol into a more declarative graph.
 *  - currently assumes that there are no cycles in the CFG!
 */
class SymbolicProtocolInterpreter(protocol: firrtl.CircuitState, stickyInputs: Boolean, solver: Solver)
  extends ProtocolInterpreter(protocol, stickyInputs) {
  import ProtocolInterpreter.Loc

  def run(): ProtocolPaths = {
    // TODO: also track sticky inputs, sticky inputs may not refer to outputs!
    val incomingFlow = mutable.HashMap[String, DataFlowInfo]()
    // for the "start" step, all args are un-mapped and the execution has not forked!
    incomingFlow("start") = DataFlowInfo(List(), args.map{ case (name, _) => name -> BigInt(0) }, false, Map())

    // we ignore final steps as they are equivalent with the first, the "start", step
    val nonFinalSteps = stepOrder.filterNot(s => steps(s._1).isFinal)
    // symbolically execute each step
    val stepsToPaths = nonFinalSteps.map { case (stepName, blockId, stmtId) =>
      val map = incomingFlow(stepName).prevMappings
      val forked = incomingFlow(stepName).hasForked || steps.get(stepName).exists(_.doFork)
      val inputs = incomingFlow(stepName).stickyInputs
      val ctx = PathCtx(List(), map, forked, List(), inputs, Map(), None)
      val paths = executeFrom(ctx, Loc(blockId, stmtId))
      // update mappings / forkInfo for all following paths
      trackFlowInfo(incomingFlow, stepName, paths.filter(p => p.next.isDefined && !p.next.contains("start")))
      stepName -> paths
    }

    ProtocolPaths(getInfo, stepsToPaths)
  }

  private def trackFlowInfo(incomingFlow: mutable.HashMap[String, DataFlowInfo], stepName: String, newPaths: Iterable[PathCtx]): Unit = {
    // update mappings / forkInfo for all following paths
    newPaths.foreach { p =>
      val next = p.next.get
      val map = p.mappedArgs
      val stickyInputs = p.inputValues.filter(_._2.sticky)
      if(incomingFlow.contains(next)) {
        val cur = incomingFlow(next)
        lazy val loc = s"coming into $next. ${cur.prevSteps} vs $stepName"
        // ensure that mappings are the same
        assert(cur.prevMappings.keySet == map.keySet, s"Inconsistent mapped args, $loc")
        cur.prevMappings.foreach { case (arg, bits) =>
          val newBits = map(arg)
          if(newBits != bits) {
            throw new RuntimeException(s"Inconsistent mapping for $arg, $loc")
          }
        }

        // ensure that forking state is the same
        if(cur.hasForked != p.hasForked) {
          throw new RuntimeException(s"Inconsistent forking, $loc")
        }

        // ensure that sticky inputs are the same
        assert(cur.stickyInputs.keySet == stickyInputs.keySet, f"Inconsistent input mappings $loc")
        cur.stickyInputs.foreach { case (input, value) =>
          if(value.value != stickyInputs(input).value) {
            val (a,b) = (value.value.toString, stickyInputs(input).value.toString)
            throw new RuntimeException(s"Inconsistent values for $input, $a vs $b, $loc")
          }
        }

        // just add the step name for debug reasons
        incomingFlow(next) = cur.copy(cur.prevSteps :+ stepName)
      } else {
        // ensure that the any new sticky inputs do not depend on any outputs
        stickyInputs.foreach { case (input, value) =>
          val syms = Analysis.findSymbols(value.value)
          val outputs = filterOutputs(syms).map(_.toString)
          assert(outputs.isEmpty, s"Input $input depends on outputs $outputs and is also sticky. The output will have a different value in the next step and thus this is not allowed!")
        }

        incomingFlow(next) = DataFlowInfo(List(stepName), map, p.hasForked, stickyInputs)
      }
    }
  }

  private def executeFrom(startCtx: PathCtx, loc: Loc): List[PathCtx] = {
    val stmts = getBlock(loc.block).drop(loc.stmt)
    if(stmts.isEmpty) { return List(startCtx) }
    var ctx = startCtx
    stmts.map{ case (l, s) => parseStmt(s, l) }.foreach {
      case s: DoStep => return List(onStep(ctx, s))
      case s: DoSet => ctx = onSet(ctx, s)
      case s: DoUnSet => ctx = onUnSet(ctx, s)
      case s: DoAssert => ctx = onAssert(ctx, s)
      case s: Goto => return onGoto(ctx, s)
    }
    throw new RuntimeException(s"Expected block to end with goto or step, not: ${stmts.last._2.serialize}")
  }

  /** Reading a symbol has different restrictions depending on its kind:
   * - args: needs to be mapped before it is used as a rvalue
   * - rets: should only be used after dependent input args have been mapped (currently just allowed ... :( )
   * - inputs: (1) if already set: just return value (2) if not set: create new random input (not supported yet)
   * - outputs: output will be added to read outputs which are used to decide whether an input can be set
   */
  private def analyzeRValue(ctx: PathCtx, e: smt.BVExpr, info: ir.Info = ir.NoInfo, isSet: Boolean = false): (PathCtx, smt.BVExpr) = {
    val syms = Analysis.findSymbols(e)

    // args
    if(!isSet) { // set maps any unmapped args
      filterArgs(syms).foreach { arg =>
        assert(isMapped(ctx, arg), s"Argument $arg needs to first be bound to an input before reading it!${info.serialize}")
      }
    }

    // Note on rets: if their corresponding args are not mapped yet, the test becomes somewhat meaningless
    //               no matter whether it is concretely or symbolically executed. However, we do not check for this...

    // inputs
    val inputReplacements = filterInputs(syms).map { i => i.name ->
      ctx.inputValues.get(i.name).map(_.value)
        .getOrElse(throw new RuntimeException(s"Input $i cannot be read before it is set!${info.serialize}"))
    }.toMap

    // outputs
    val newOutputs = filterOutputs(syms).filterNot(o => ctx.outputsRead.contains(o.name))
      .map(o => o.name -> OutputRead(o.name, info))

    val newExpr = replace(e, inputReplacements).asInstanceOf[smt.BVExpr]
    val newCtx = ctx.copy(outputsRead = ctx.outputsRead ++ newOutputs)
    (newCtx, newExpr)
  }

  private def onSet(ctx: PathCtx, set: DoSet): PathCtx = {
    val (c1, value) = analyzeRValue(ctx, toSMT(set.expr, inputs(set.loc), allowNarrow = true), set.info, isSet=true)
    //println(f"SET ${set.loc} <= $value ${set.info.serialize}")
    val inp = InputValue(set.loc, value, set.isSticky, set.info)
    c1.copy(inputValues = c1.inputValues + (set.loc -> inp))
  }

  private def onUnSet(ctx: PathCtx, unset: DoUnSet): PathCtx = {
    //println(f"UNSET ${unset.loc} ${unset.info.serialize}")
    // TODO: check if we remove a mapping of an argument that was read
    ctx.copy(inputValues = ctx.inputValues - unset.loc)
  }

  private def onAssert(ctx: PathCtx, a: DoAssert): PathCtx = {
    val (c1, expr) = analyzeRValue(ctx, toSMT(a.expr), a.info)
    //println(f"ASSERT $expr ${a.info.serialize}")
    c1.copy(asserts = c1.asserts :+ expr)
  }

  private def onGoto(ctx: PathCtx, g: Goto): List[PathCtx] = {
    val (c1, cond) = analyzeRValue(ctx, toSMT(g.cond), g.info)

    if(cond == smt.True()) { // just a GOTO, not a branch!
      assert(g.alt == -1)
      executeFrom(c1, Loc(g.conseq, 0))
    } else { // actually a branch
      //println(f"IF $cond GOTO ${g.conseq} ELSE ${g.alt}")

      // execute true path
      val truPath = c1.cond :+ cond
      val truCtxs = if(isFeasible(smt.BVAnd(truPath))) {
        executeFrom(c1.copy(cond = truPath), Loc(g.conseq, 0))
      } else { List() }

      // execute false path
      val falsPath = c1.cond :+ smt.BVNot(cond)
      val falsCtxs = if(isFeasible(smt.BVAnd(falsPath))) {
        executeFrom(c1.copy(cond = falsPath), Loc(g.alt, 0))
      } else { List() }

      truCtxs ++ falsCtxs
    }
  }

  private def onStep(ctx: PathCtx, step: DoStep): PathCtx = {
    //println(f"STEP @ ${step.loc} ${step.info.serialize}")
    // final steps are equivalent to the start step
    val name = if(steps(step.name).isFinal) { "start" } else { step.name }
    ctx.copy(next = Some(name))
  }

  private def toSMT(expr: ir.Expression, width: Int = 1, allowNarrow: Boolean = false): smt.BVExpr = {
    val e = ExpressionConverter.toMaltese(expr, width, allowNarrow)
    // we simplify once, after converting FIRRTL to SMT
    simplify(e)
  }
  private def simplify(e: smt.BVExpr): smt.BVExpr = smt.SMTSimplifier.simplify(e).asInstanceOf[smt.BVExpr]
  private def replace(e: smt.SMTExpr, subs: Map[String, smt.SMTExpr]): smt.SMTExpr = e match {
    case s : smt.BVSymbol => subs.getOrElse(s.name, s)
    case other => other.mapExpr(replace(_, subs))
  }
  private def filterInputs(e: List[smt.SMTSymbol]): Iterable[smt.SMTSymbol] = e.filter(s => inputs.contains(s.name))
  private def filterOutputs(e: List[smt.SMTSymbol]): Iterable[smt.SMTSymbol] = e.filter(s => outputs.contains(s.name))
  private def filterArgs(e: List[smt.SMTSymbol]): Iterable[smt.SMTSymbol] = e.filter(s => args.contains(s.name))
  private def filterRets(e: List[smt.SMTSymbol]): Iterable[smt.SMTSymbol] = e.filter(s => rets.contains(s.name))
  private def isMapped(ctx: PathCtx, arg: smt.SMTSymbol): Boolean = {
    require(args.contains(arg.name))
    val allBits = (BigInt(1) << args.asInstanceOf[smt.BVSymbol].width) - 1
    ctx.mappedArgs.get(arg.name).contains(allBits)
  }
  private def isFeasible(cond: smt.BVExpr): Boolean = solver.check(cond, produceModel = false).isSat
}