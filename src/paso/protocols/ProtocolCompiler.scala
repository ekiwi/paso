// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.annotations._
import firrtl.graph.DiGraph
import firrtl._
import firrtl.options.Dependency
import firrtl.passes.PassException
import firrtl.stage.{Forms, TransformManager}

import scala.collection.mutable

object ProtocolCompiler {
  private val passes = Seq(
    Dependency(CheckStatementsPass),
    Dependency(InlineNodesPass),
    Dependency(ProtocolPrefixingPass),
    Dependency[GotoProgramTransform],
    Dependency(EnsureFinalStepPass),
    Dependency(StepOrderPass))
  private val compiler = new TransformManager(passes)

  def run(state: CircuitState, ioPrefix: String, specPrefix: String, methodName: String, doTrace: Boolean): CircuitState = {
    if(doTrace) {
      println("Before Protocol Compilation")
      println(state.circuit.serialize)
      println()
    }
    val annos = Set(ProtocolPrefixAndNameAnnotation(ioPrefix, specPrefix, methodName))
    val st = state.copy(annotations = state.annotations ++ annos)
    val r = compiler.runTransform(st)
    if(doTrace) {
      println("After Protocol Compilation")
      println(r.circuit.serialize)
    }
    r
  }
}

/** Inlines all nodes. */
object InlineNodesPass extends Transform with DependencyAPIMigration {
  // we need bundles and vectors to be lowered (=> all nodes have ground type)
  override def prerequisites = Seq(Dependency(firrtl.passes.LowerTypes))
  override def invalidates(a: Transform) = false
  // we must run before whens are removed
  override def optionalPrerequisiteOf = Seq(Dependency(firrtl.passes.ExpandWhens))

  override protected def execute(state: CircuitState): CircuitState = {
    state.copy(circuit = state.circuit.mapModule(onModule))
  }

  private def onModule(m: ir.DefModule): ir.DefModule = m match {
    case e : ir.ExtModule => e
    case mod : ir.Module =>
      val nodes = mutable.HashMap[String, ir.Expression]()
      mod.mapStmt(onStmt(nodes))

  }

  private def onStmt(nodes: mutable.HashMap[String, ir.Expression])(s: ir.Statement): ir.Statement =
    s.mapStmt(onStmt(nodes)).mapExpr(onExpr(nodes.get)) match {
    case ir.DefNode(_, name, value) => nodes(name) = value ; ir.EmptyStmt
    // remove trivially true or false conditionals
    case ir.Conditionally(_, Utils.True(), conseq, _) => conseq
    case ir.Conditionally(_, Utils.False(), _, alt) => alt
    case other => other
  }

  private def onExpr(nodes: String => Option[ir.Expression])(expr: ir.Expression): ir.Expression = expr.mapExpr(onExpr(nodes)) match {
    case r @ ir.Reference(name, tpe, _, _) => nodes(name) match {
      case Some(e) => assert(e.tpe == tpe) ; e
      case None => r
    }
    // limited constant prop for boolean expressions
    case ir.DoPrim(PrimOps.Not, Seq(e), Seq(), Utils.BoolType) => Utils.not(e)
    case ir.DoPrim(PrimOps.And, Seq(a, b), Seq(), Utils.BoolType) => Utils.and(a, b)
    case ir.DoPrim(PrimOps.Or, Seq(a, b), Seq(), Utils.BoolType) => Utils.or(a, b)
    case ir.DoPrim(PrimOps.Eq, Seq(a, b), Seq(), Utils.BoolType) if a.serialize == b.serialize => Utils.True()
    case other => other
  }
}

case class ProtocolPrefixAndNameAnnotation(ioPrefix: String, specPrefix: String, methodName: String) extends NoTargetAnnotation {
  val methodPrefix =  f"$specPrefix${methodName}_"
  assert(ioPrefix != methodPrefix, "Prefixes need to be distinguishable")
}

/** Prefixes the protocol IO according to the ProtocolPrefixAnnotation:
 * - e.g.: "io_start" -> "$ioPrefix_start" (io is removed)
 * - e.g.: "arg_a" -> "${methodPrefix}arg_a" (for method we just prepend)
 * */
object ProtocolPrefixingPass extends Transform with DependencyAPIMigration {
  // we need bundles and vectors to be lowered
  override def prerequisites = Seq(Dependency(firrtl.passes.LowerTypes))
  override def invalidates(a: Transform) = false

  // we need to run right before turning things into a goto program since firrtl passes won't necessarily deal will
  // with out prefixing (the `.` in the prefixes means we produce illegal firrtl identifiers)
  override def optionalPrerequisiteOf = Seq(Dependency[GotoProgramTransform])
  override def optionalPrerequisites = Seq(Dependency(InlineNodesPass))

  override protected def execute(state: CircuitState): CircuitState = {
    val anno = state.annotations.collectFirst{ case a : ProtocolPrefixAndNameAnnotation => a } match {
      case Some(a) => a
      case None => return state
    }

    assert(state.circuit.modules.size == 1, "Protocols should never have submodules!")
    val m = state.circuit.modules.head.asInstanceOf[ir.Module]

    val (ioPorts, notIOPorts) = m.ports.partition(_.name.startsWith("io_"))
    val methodPorts = notIOPorts.filterNot(p => p.name == "clock" || p.name == "reset")
      .filter(p => p.name.startsWith("arg") || p.name.startsWith("ret"))
    //methodPorts.foreach { p =>
    //  assert(p.name.startsWith("arg") || p.name.startsWith("ret"), f"Unexpected port: ${p.serialize}")
    //}

    val renames = (ioPorts.map(p => p.name -> (anno.ioPrefix + p.name.substring(2))) ++
      methodPorts.map(p => p.name -> (anno.methodPrefix + p.name))).toMap

    val renamedPorts = m.mapPort(p => renames.get(p.name).map(n => p.copy(name = n)).getOrElse(p))
    val renamedExpr = renamedPorts.mapStmt(onStmt(renames))

    state.copy(circuit = state.circuit.copy(modules = List(renamedExpr)))
  }

  private def onStmt(renames: Map[String,String])(s: ir.Statement): ir.Statement =
    s.mapExpr(onExpr(renames)).mapStmt(onStmt(renames))
  private def onExpr(renames: Map[String,String])(e: ir.Expression): ir.Expression = e match {
    case r @ ir.Reference(name, _, _, _) if renames.contains(name) => r.copy(name = renames(name))
    case other => other.mapExpr(onExpr(renames))
  }
}
/** Turns the body of the main module into a goto program similar to CBMC's internal representation (or LLVM IR).
 *  - the basic blocks are encoded in the main body which will contain a block of blocks, with each inner block
 *    representing a basic block
 *  - basic blocks are zero-indexed
 *  - the (conditional) [[Goto]] statement encodes the next block ids which correspond to the block indices!
 * */
class GotoProgramTransform extends Transform with DependencyAPIMigration {
  // we need bundles and vectors to be lowered
  override def prerequisites = Seq(Dependency(firrtl.passes.LowerTypes))
  override def invalidates(a: Transform) = false

  // we must run before whens are removed
  override def optionalPrerequisiteOf = Seq(Dependency(firrtl.passes.ExpandWhens))
  // nodes must be inlined first!
  override def optionalPrerequisites = Seq(Dependency(InlineNodesPass))

  //
  private val statements = mutable.ArrayBuffer[ir.Statement]()
  private val blocks = mutable.ArrayBuffer[(Int, ir.Block)]()
  private var activeBlockId = 0
  private var blockIdCounter = 1
  private def finishBlock(nextBlockId: Int): Unit = {
    blocks.append((activeBlockId, ir.Block(statements.toVector)))
    statements.clear()
    activeBlockId = nextBlockId
    statements.append(BlockId(nextBlockId))
  }
  private def resetState(): Unit = {
    statements.clear()
    blocks.clear()
    activeBlockId = 0
    blockIdCounter = 1
    statements.append(BlockId(0))
  }

  override protected def execute(state: CircuitState): CircuitState = {
    assert(state.circuit.modules.size == 1, "Protocols should never have submodules!")
    val m = state.circuit.modules.head.asInstanceOf[ir.Module]

    // generate blocks by visiting all statements
    resetState()
    onStmt(m.body)
    finishBlock(-1)

    // turn blocks into an array that is indexed by block id
    val sortedBlocks = blocks.sortBy(_._1)
    val blockArray = sortedBlocks.map(_._2).toArray
    // replace body of module with our blocks
    val mGoto = m.copy(body = ir.Block(blockArray))

    //println(mGoto.serialize)

    state.copy(circuit = state.circuit.copy(modules = List(mGoto)))
  }
  private def onStmt(s: ir.Statement): Unit = s match {
    case ir.Conditionally(info, pred, conseq, alt) =>
      val altIsEmpty = alt == ir.EmptyStmt
      // reserve ids
      val conseqId = blockIdCounter ; blockIdCounter += (if(altIsEmpty) 2 else 3)
      // add goto statement and finish current block
      statements.append(Goto(info, pred, conseqId, conseqId + 1))
      // make conseq block
      finishBlock(conseqId)
      onStmt(conseq)
      // make alt if it is not empty
      if(!altIsEmpty) {
        statements.append(Goto(info, conseqId + 2))
        finishBlock(conseqId + 1)
        onStmt(alt)
        statements.append(Goto(info, conseqId + 2))
        // start block after when:
        finishBlock(conseqId + 2)
      } else {
        statements.append(Goto(info, conseqId + 1))
        // start block after when:
        finishBlock(conseqId + 1)
      }
    case ir.Block(stmts) => stmts.foreach(onStmt)
    case ir.EmptyStmt => // ignore empty statements
    case other => statements.append(other)
  }
}

/** checks to make sure that the protocol ends in a step */
object EnsureFinalStepPass extends Transform with DependencyAPIMigration {
  // we need to run on the goto program
  override def prerequisites = Seq(Dependency[GotoProgramTransform])
  override def optionalPrerequisiteOf = Seq(Dependency(StepOrderPass))
  override def invalidates(a: Transform) = false

  override protected def execute(state: CircuitState): CircuitState = {
    val isStep = (state.annotations.collect { case s : StepAnnotation => s.target.ref } :+ "start").toSet
    val m = state.circuit.modules.head.asInstanceOf[ir.Module]
    val bbs = m.body.asInstanceOf[ir.Block].stmts.map(_.asInstanceOf[ir.Block].stmts)
    val finalBlock = findFinalBlock(bbs)(0)
    val lastStmtIsStep = bbs(finalBlock).last match {
      case ir.DefWire(_, name, _) if isStep(name) => true
      case _ => false
    }
    // if the goto program already ends in a step, there is nothing to do here
    if(!lastStmtIsStep) {
      val msg = "Protocols need to end in a clock step!\n" + m.serialize
      throw new ProtocolError(msg)
    }

    state
  }

  private def findFinalBlock(blocks: Seq[Seq[ir.Statement]])(block: Int): Int = {
    assert(block >= 0)
    val stmts = blocks(block).drop(1) // ignore block id
    stmts.collectFirst {
      case Goto(_, _, a, b) if b >= 0 =>
        val (x, y) = (findFinalBlock(blocks)(a), findFinalBlock(blocks)(b))
        assert(x == y) ; x
      case Goto(_, _, a, _) => findFinalBlock(blocks)(a)
    }.getOrElse(block)
  }
}

// contains the names of all steps in topological order
case class StepOrderAnnotation(steps: Seq[(String, Int, Int)], longestPath: Int) extends NoTargetAnnotation

/** adds a topological order for steps */
object StepOrderPass extends Transform with DependencyAPIMigration {
  // we need to run on the goto program
  override def prerequisites = Seq(Dependency[GotoProgramTransform])
  override def invalidates(a: Transform) = false

  override protected def execute(state: CircuitState): CircuitState = {
    val isStep = (state.annotations.collect { case s : StepAnnotation => s.target.ref } :+ "start").toSet
    val m = state.circuit.modules.head.asInstanceOf[ir.Module]
    val bbs = m.body.asInstanceOf[ir.Block].stmts.map(_.asInstanceOf[ir.Block].stmts)
    val steps = ("start", 0, 0) +: findSteps(bbs, isStep)
    val stepEdges = steps.map { case (name, blockId, stmtId) =>
      name -> findNextStep(bbs, isStep)(blockId, stmtId).toSet
    }
    val stepEdgeMap = stepEdges.toMap
    val stepGraph = DiGraph[String](stepEdgeMap)
    val stepOrder = stepGraph.linearize
    val stepMap = steps.map(s => s._1 -> s).toMap
    val longestPath = findLongestPath(stepEdgeMap)("start")
    val anno = StepOrderAnnotation(stepOrder.map(stepMap), longestPath)
    // final steps have no next step
    val finalSteps = stepEdges.filter(_._2.isEmpty).map(_._1).toSet
    // change annotation for final steps
    val (stepAnnos, otherAnnos) = state.annotations.partition(_.isInstanceOf[StepAnnotation])
    stepAnnos.collect{ case a : StepAnnotation => a }
      .foreach(a => assert(!a.isFinal, f"Should not have been marked as final yet! ${a.target}"))
    val newStepAnnos = stepAnnos.map{ case a : StepAnnotation => a.copy(isFinal = finalSteps.contains(a.target.ref)) }

    state.copy(annotations = otherAnnos ++ newStepAnnos :+ anno)
  }

  private def findNextStep(blocks: Seq[Seq[ir.Statement]], isStep: String => Boolean)(block: Int, stmt: Int): List[String] = {
    assert(block >= 0)
    val stmts = blocks(block).drop(1) // ignore block id
    stmts.drop(stmt).collectFirst {
      case ir.DefWire(_, name, _) if isStep(name) => List(name)
      case Goto(_, _, a, b) if b >= 0 => findNextStep(blocks, isStep)(a, 0) ++ findNextStep(blocks, isStep)(b, 0)
      case Goto(_, _, a, _) => findNextStep(blocks, isStep)(a, 0)
    }.getOrElse(List())
  }

  private def findSteps(blocks: Seq[Seq[ir.Statement]], isStep: String => Boolean): Seq[(String, Int, Int)] = {
    blocks.zipWithIndex.flatMap { case (stmts, blockId) =>
      // ignore block id (first statement)
      stmts.drop(1).zipWithIndex.collect { case (ir.DefWire(_, name, _), stmtId) if isStep(name) => (name, blockId, stmtId+1)}
    }
  }

  private def findLongestPath(stepEdgeMap: Map[String, Set[String]])(step: String): Int = {
    val next = stepEdgeMap(step)
    if(next.isEmpty) 0 else next.toList.map(findLongestPath(stepEdgeMap)).max + 1
  }
}

object CheckStatementsPass extends Transform with DependencyAPIMigration {
  override def prerequisites = Forms.Resolved
  override def invalidates(a: Transform) = false
  override protected def execute(state: CircuitState): CircuitState = {
    state.circuit.foreachModule(onModule(_, state.annotations))
    // this is purely a checking transform which has no effect
    state
  }
  private def onModule(m: ir.DefModule, annos: AnnotationSeq): Unit = {
    val allowedWires = annos.collect {
      case s : StepAnnotation if s.target.module == m.name => s.target.ref
    }.toSet
    m.foreachStmt(onStmt(_, allowedWires))
  }
  private def onStmt(s: ir.Statement, allowedWires: Set[String]): Unit = s match {
    case ir.DefWire(info, name, _) if !allowedWires.contains(name) =>
      throw new ProtocolError(s"Cannot declare wire $name in protocol (${info.serialize}")
    case ir.DefInstance(info, name, module, _) =>
      throw new ProtocolError(s"Cannot declare instance $name of $module in protocol (${info.serialize}")
    case ir.DefMemory(info, name, _, _, _, _, _, _, _, _) =>
      throw new ProtocolError(s"Cannot declare memory $name in protocol (${info.serialize}")
    case ir.DefRegister(info, name, _, _, _, _) =>
      throw new ProtocolError(s"Cannot declare register $name in protocol (${info.serialize}")
    case ir.Attach(info, _) =>
      throw new ProtocolError(s"Cannot use analog signals in protocol (${info.serialize}")
    case ir.Print(info, _, _, _, _) =>
      throw new ProtocolError(s"Cannot use the print statement in protocol (${info.serialize}")
    case ir.Verification(ir.Formal.Assume, info, _, _, _, _) =>
      throw new ProtocolError(s"Cannot use the assume statement in protocol (might be worth considering though) (${info.serialize}")
    case ir.Verification(ir.Formal.Cover, info, _, _, _, _) =>
      throw new ProtocolError(s"Cannot use the cover statement in protocol (${info.serialize}")
    case ir.Stop(info, _, _, _) =>
      throw new ProtocolError(s"Cannot use the stop statement in protocol (${info.serialize}")
    case other => other.foreachStmt(onStmt(_, allowedWires))
  }
}

class ProtocolError(s: String) extends PassException(s)
