// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import firrtl.{AnnotationSeq, CircuitState, DependencyAPIMigration, Transform, ir}
import firrtl.options.Dependency
import firrtl.passes.PassException
import firrtl.stage.{Forms, TransformManager}

import scala.collection.mutable

object ProtocolCompiler {
  private val passes = Seq(Dependency(CheckStatementsPass), Dependency[ProtocolNormalizationPass])
  private val compiler = new TransformManager(passes)

  def run(state: CircuitState): CircuitState = {
    compiler.runTransform(state)
  }
}

/** Normalizes a protocol program to make it easier to interpret.
 * One transformation we do is to turn the Conditionally statements into custom Goto statements
 * */
class ProtocolNormalizationPass extends Transform with DependencyAPIMigration {
  // we need bundles and vectors to be lowered
  override def prerequisites = Seq(Dependency(firrtl.passes.LowerTypes))
  override def invalidates(a: Transform) = false

  // we must run before whens are removed
  override def optionalPrerequisiteOf = Seq(Dependency(firrtl.passes.ExpandWhens))

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

    println(mGoto.serialize)

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
    case other => statements.append(other)
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
      case ForkAnnotation(target) if target.module == m.name => target.ref
      case StepAnnotation(target) if target.module == m.name => target.ref
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
