// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.backends.experimental.smt.ExpressionConverter
import firrtl.ir
import maltese.smt
import maltese.smt.solvers.Yices2

import scala.collection.mutable

/** represents a "cycle" (the period between two state transitions) of the protocol:
 * - all assertions over the outputs in this cycle are encoded as boolean formulas with the input constraints as guards
 *   like: `in := 1 ; assert(out == 2)` gets encoded as `(in = 1) => (out = 2)`
 * - the final input assumptions, i.e. the stable input signals that will determine the next state are also
 *   encoded separately as guarded assumptions. The guard in this case is the path condition.
 *   ```
 *   in := 1
 *   when c:
 *     in := 2
 *   ```
 *   results in: `(c => (in = 2)) and (not(c) => (in = 1))`
 *   it might be better to encode this as `in = ite(c, 2, 1)` ...
 * - final input assumptions depend on the same path guards as the next cycle
 * - there could be different next cycles depending on ret/arg or module i/o, these are encoded as a priority list
 *   with guards that need to be evaluated from front to back, the first guard which is true is the transition that
 *   should be taken
 * - TODO: encode mapping of method args (the first time args are applied to the inputs, they are treated as a mapping,
 *         after that they are a constraint)
 * */
case class Cycle(name: String, assertions: List[Guarded], assumptions: List[Guarded], mappings: List[Guarded], next: List[Next])

case class Guarded(guards: List[smt.BVExpr], pred: smt.BVExpr) {
  def toExpr: smt.BVExpr = if(guards.isEmpty) { pred } else {
    smt.BVImplies(smt.BVAnd(guards), pred)
  }
}

case class Next(guard: smt.BVExpr, fork: Boolean, cycleId: Int)

/** the first cycle is always cycles.head */
case class ProtocolGraph(name: String, cycles: Array[Cycle])


/** Encodes imperative protocol into a more declarative graph.
 *  - currently assumes that there are no cycles in the CFG!
 */
class SymbolicProtocolInterpreter(protocol: firrtl.CircuitState, stickyInputs: Boolean = false) extends ProtocolInterpreter(protocol) {
  import ProtocolInterpreter.Loc

  // predicates that "guard" the current instructions
  private val guards = mutable.ArrayBuffer[smt.BVExpr]()
  private def guardExpr = guards.foldLeft[smt.BVExpr](smt.True())((a,b) => smt.BVAnd(a, b))

  // keep track of steps we still need to visit
  private val stepsToProcess = mutable.ArrayStack[StepInfo]()
  private var stepCount = 1

  // build a "cycle"
  private var cycle = Cycle("", List(), List(), List(), List())

  def run(): ProtocolGraph = {
    // we start with the implicit starting step
    stepsToProcess.clear()
    stepsToProcess.push(StepInfo("start", Loc(0,0), 0))
    stepCount = 1

    println(s"Step Order: ${stepOrder}")

    while(stepsToProcess.nonEmpty) {
      val step = stepsToProcess.pop()
      println(s"Processing ${step.name}")
      val prevMappings = args.map{ case (name, _) => name -> BigInt(0) }.toMap
      val ctx = PathCtx(smt.True(), prevMappings, List(), Map(), Map(), None)
      val paths = executeFrom(ctx, step.loc)
      println(s"Found ${paths.size} paths for ${step.name}")
    }

    // TODO: actual graph!
    ProtocolGraph(name, Array())
  }

  private def executeFrom(startCtx: PathCtx, loc: Loc): List[PathCtx] = {
    var ctx = startCtx
    val stmts = getBlock(loc.block).drop(loc.stmt)
    stmts.map{ case (l, s) => parseStmt(s, l) }.foreach {
      case s: DoStep =>
        // return final ctx
        return List(onStep(ctx, s, loc.stmt + 1 == stmts.length))
      case s: DoSet => ctx = onSet(ctx, s)
      case s: DoUnSet => ctx = onUnSet(ctx, s)
      case s: DoAssert => ctx = onAssert(ctx, s)
      case s: Goto => return onGoto(ctx, s)
    }
    // TODO: if we get here, that means that we reached the end of the protocol
    List(ctx)
  }

  /** Reading a symbol has different restrictions depending on its kind:
   * - args: needs to be mapped before it is used as a rvalue; TODO: different effect when used on rhs of set
   * - rets: should only be used after dependent input args have been mapped (currently just allowed ... :( )
   * - inputs: (1) if already set: just return value (2) if not set: create new random input (not supported yet)
   * - outputs: output will be added to read outputs which are used to decide whether an input can be set
   */
  private def analyzeRValue(ctx: PathCtx, e: smt.BVExpr, info: ir.Info = ir.NoInfo, isSet: Boolean = false): (PathCtx, smt.BVExpr) = {
    val syms = findSymbols(e)

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
      val truPath = simplify(smt.BVAnd(c1.cond, cond))
      val truCtxs = if(isFeasible(truPath)) {
        executeFrom(c1.copy(cond = truPath), Loc(g.conseq, 0))
      } else { List() }

      // execute false path
      val falsPath = simplify(smt.BVAnd(c1.cond, smt.BVNot(cond)))
      val falsCtxs = if(isFeasible(falsPath)) {
        executeFrom(c1.copy(cond = falsPath), Loc(g.alt, 0))
      } else { List() }

      truCtxs ++ falsCtxs
    }
  }

  private def onStep(ctx: PathCtx, step: DoStep, isLast: Boolean): PathCtx = {
    val id = if(isLast) { -1 } else {
      val id = stepsToProcess.find(_.name == step.name).map(_.id).getOrElse(stepCount)
      if(id == stepCount) {
        stepCount += 1
        val nextLoc = step.loc.copy(stmt = step.loc.stmt + 1)
        stepsToProcess.push(StepInfo(step.name, nextLoc, id))
      }
      id
    }
    val next = Next(guardExpr, step.fork, id)
    //println(f"STEP @ ${step.loc} ${step.info.serialize}")
    ctx.copy(next = Some(next))
  }

  private def toSMT(expr: ir.Expression, width: Int = 1, allowNarrow: Boolean = false): smt.BVExpr = {
    val e = ExpressionConverter.toMaltese(expr, width, allowNarrow)
    // we simplify once, after converting FIRRTL to SMT
    simplify(e)
  }
  private def simplify(e: smt.BVExpr): smt.BVExpr = smt.SMTSimplifier.simplify(e).asInstanceOf[smt.BVExpr]
  private def findSymbols(e: smt.SMTExpr): List[smt.SMTSymbol] = e match {
    case s: smt.BVSymbol => List(s)
    case s: smt.ArraySymbol => List(s)
    case other => other.children.flatMap(findSymbols)
  }
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
  private val solver = Yices2()
  private def isFeasible(cond: smt.BVExpr): Boolean = solver.check(cond, produceModel = false).isSat
}

private case class StepInfo(name: String, loc: ProtocolInterpreter.Loc, id: Int)

private case class InputValue(name: String, value: smt.BVExpr, sticky: Boolean, info: ir.Info = ir.NoInfo)
private case class OutputRead(name: String, info: ir.Info = ir.NoInfo)

private case class PathCtx(
  cond: smt.BVExpr, prevMappings: Map[String, BigInt], asserts: List[smt.BVExpr],
  inputValues: Map[String, InputValue], outputsRead: Map[String, OutputRead],
  next: Option[Next]
) {
  def mappedArgs: Map[String, BigInt] = {
    val updates =
      inputValues.flatMap{ case (_, v) => BitMapping.mappedBits(v.value) }
        .filter{ case (name, _) => prevMappings.contains(name) }
    updates.foldLeft(prevMappings){ case (map, (name, bits)) => map + (name -> (map.getOrElse(name, BigInt(0)) | bits)) }
  }
}