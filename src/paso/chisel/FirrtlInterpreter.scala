// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import chisel3.util.log2Ceil
import firrtl.annotations.Annotation
import firrtl.ir
import paso.AssertAnnotation
import uclid.smt


import scala.collection.mutable

object FirrtlInterpreter {
  def run(stmt: ir.Statement): Unit = new FirrtlInterpreter().onStmt(stmt)
  def run(m: ir.Module): Unit = new FirrtlInterpreter().onModule(m)
}

object firrtlToSmtType {
  private def getBitVecType(width: BigInt): smt.Type = {
    require(width > 0, "Zero width wires are not supported")
    if(width == 1) smt.BoolType else smt.BitVectorType(width.toInt)
  }
  def apply(t: ir.Type): smt.Type = t match {
    case ir.UIntType(ir.IntWidth(w)) => getBitVecType(w)
    case ir.SIntType(ir.IntWidth(w)) => getBitVecType(w)
    case ir.ResetType => smt.BoolType
    case ir.ClockType => smt.BoolType
    case ir.VectorType(tpe, size) => smt.ArrayType(List(getBitVecType(log2Ceil(size))), apply(tpe))
    case other => throw new NotImplementedError(s"TODO: implement conversion for $other")
  }
  def apply(dataType: ir.Type, depth: BigInt): smt.Type = {
    val indexType = smt.BitVectorType(log2Ceil(depth))
    smt.ArrayType(List(indexType), apply(dataType))
  }
}

class FirrtlInterpreter extends SmtHelpers {
  val refs = mutable.HashMap[String, smt.Expr]()
  val connections = mutable.HashMap[String, Seq[(smt.Expr, smt.Expr)]]()
  val inputs = mutable.HashMap[String, smt.Type]()
  val outputs = mutable.HashMap[String, smt.Type]()
  val regs = mutable.HashMap[String, smt.Type]()
  val mems = mutable.HashMap[String, smt.Type]()
  val wires = mutable.HashMap[String, smt.Type]()
  private val cond_stack = mutable.Stack[smt.Expr]()
  def pathCondition: smt.Expr = cond_stack.foldLeft[smt.Expr](smt.BooleanLit(true))((a,b) => app(smt.ConjunctionOp, a, b))

  def isInput(name: String): Boolean = inputs.contains(name)
  def isInput(sym: smt.Symbol): Boolean = inputs.get(sym.id).exists(_ == sym.typ)
  def isInput(e: smt.Expr): Boolean = e match { case s: smt.Symbol => isInput(s) case _ => false }
  def isOutput(name: String): Boolean = outputs.contains(name)
  def isOutput(sym: smt.Symbol): Boolean = outputs.get(sym.id).exists(_ == sym.typ)
  def isOutput(e: smt.Expr): Boolean = e match { case s: smt.Symbol => isOutput(s) case _ => false }
  def isIO(name: String): Boolean = isInput(name) || isOutput(name)

  def getWidth(t: smt.Type): Int = t match {
    case smt.BitVectorType(w) => w
    case smt.BoolType => 1
    case other => throw new RuntimeException(s"$other has no width")
  }
  def getWidth(t: ir.Type): Int = t match {
    case ir.SIntType(w) => getWidth(w)
    case ir.UIntType(w) => getWidth(w)
    case other => throw new RuntimeException(s"$other has no width")
  }
  def getWidth(w: ir.Width): Int = w match {
    case ir.IntWidth(width) => width.toInt
    case ir.UnknownWidth => throw new NotImplementedError("TODO: better width inference")
  }
  def isSigned(t: ir.Type): Boolean = t match {
    case ir.SIntType(_) => true
    case _ => false
  }

  def onType(t: ir.Type): smt.Type = firrtlToSmtType(t)

  // most important to customize
  def onAssign(name: String, expr: smt.Expr): Unit = {}
  def onReference(r: ir.Reference): smt.Expr = refs(r.name)
  def onSubfield(r: ir.SubField): smt.Expr = refs(r.serialize)
  def onSubAccess(array: smt.Expr, index: ir.Expression): smt.Expr = {
    val indexWidth = array.typ.asInstanceOf[smt.ArrayType].inTypes.head.asInstanceOf[smt.BitVectorType].width
    select(array, onExpr(index, indexWidth))
  }
  def getInvalid(width: Int): smt.Expr = if(width == 1) smt.BooleanLit(false) else smt.BitVectorLit(0, width)
  private def defX(name: String, tpe: smt.Type, registry: mutable.HashMap[String, smt.Type]): Unit = {
    require(!refs.contains(name))
    refs(name) = smt.Symbol(name, tpe)
    connections(name) = Seq()
    registry(name) = tpe
  }
  def defWire(name: String, tpe: ir.Type): Unit = defX(name, onType(tpe), wires)
  def defReg(name: String, tpe: ir.Type): Unit = defX(name, onType(tpe), regs)
  def defMem(name: String, tpe: ir.Type, depth: BigInt): Unit =
    defX(name, smt.ArrayType(List(smt.BitVectorType(log2Ceil(depth))), onType(tpe)), mems)
  def defNode(name: String, value: smt.Expr): Unit = {
    onAssign(name, value)
    require(!refs.contains(name))
    refs(name) = value
  }
  def onWhen(cond: smt.Expr, tru: ir.Statement, fals: ir.Statement): Unit = {
    cond_stack.push(cond)
    onStmt(tru)
    cond_stack.pop()
    cond_stack.push(app(smt.NegationOp, cond))
    onStmt(fals)
    cond_stack.pop()
  }

  // extends expression to width
  def onExpr(e: ir.Expression, width: Int): smt.Expr =
    if(isSigned(e.tpe)) sext(onExpr(e), width) else zext(onExpr(e), width)

  // extends expressions to be the same length
  def onExpr(e1: ir.Expression, e2: ir.Expression): Tuple2[smt.Expr, smt.Expr] = {
    require(isSigned(e1.tpe) == isSigned(e2.tpe), s"$e1 : ${e1.tpe} vs $e2 : ${e2.tpe}")
    val (s1, s2) = (onExpr(e1), onExpr(e2))
    val width = Seq(getWidth(s1.typ), getWidth(s2.typ)).max
    if(isSigned(e1.tpe)) (sext(s1, width), sext(s2, width))
    else (zext(s1, width), zext(s2, width))
  }

  private def onLiteral(value: BigInt, width: Int): smt.Expr = {
    require(width > 0, "Zero width wires are not supported")
    if(width == 1) smt.BooleanLit(value != 0) else smt.BitVectorLit(value, width)
  }

  def onExpr(e: ir.Expression): smt.Expr = e match {
    case r: ir.Reference => onReference(r)
    case firrtl.WRef(name, tpe, _, _) => onReference(ir.Reference(name, tpe))
    case r: ir.SubField => onSubfield(r)
    case firrtl.WSubField(expr, name, tpe, _) => onSubfield(ir.SubField(expr, name, tpe))
    case ir.SubIndex(expr, value, _) => select(onExpr(expr), value)
    case firrtl.WSubIndex(expr, value, tpe, _) => select(onExpr(expr), value)
    // TODO: handle out of bounds accesses gracefully
    case ir.SubAccess(expr, index, tpe) => onSubAccess(onExpr(expr), index)
    case firrtl.WSubAccess(expr, index, tpe, _) => onSubAccess(onExpr(expr), index)
    case ir.Mux(cond, tval, fval, _) =>
      val args = onExpr(tval, fval)
      ite(onExpr(cond, 1), args._1, args._2)
    case ir.ValidIf(cond, value, tpe) =>
      val sv = onExpr(value)
      ite(onExpr(cond, 1), sv, getInvalid(getWidth(sv.typ)))
    case ir.UIntLiteral(value, width) => onLiteral(value, getWidth(width))
    case ir.SIntLiteral(value, width) => onLiteral(value, getWidth(width))
    case ir.DoPrim(op, Seq(a, b), Seq(), tpe) =>
      BinOpCompiler.compile(op, a.tpe, b.tpe, tpe)._2(onExpr(a), onExpr(b))
    case ir.DoPrim(op, Seq(a), consts, tpe) =>
      UnOpCompiler.compile(op, a.tpe, tpe, consts)._2(onExpr(a))
    case ir.DoPrim(op, args, consts, tpe) =>
      throw new NotImplementedError(s"TODO: DoPrim($op, $args, $consts, $tpe)")
    case _ : ir.FixedLiteral =>
      throw new NotImplementedError("TODO: fixed point support")
    case other =>
      throw new NotImplementedError(s"TODO: implement $other")
  }

  def onConnect(lhs: String, rhs: smt.Expr): Unit = {
    onAssign(lhs, rhs)
    if(!isIO(lhs)) {
      connections(lhs) = connections(lhs) ++ Seq((pathCondition, rhs))
    }
  }
  def onConnect(lhs: String, index: Int, rhs: smt.Expr): Unit = {
    //println(s"$lhs[$index] := $rhs")
    val st = store(smt.Symbol(lhs, rhs.typ), index, rhs)
    onAssign(lhs, st)
    if(!isIO(lhs)) {
      connections(lhs) = connections(lhs) ++ Seq((pathCondition, st))
    }
  }
  def onConnect(lhs: String, index: smt.Expr, rhs: smt.Expr): Unit = {
    //println(s"$lhs[$index] := $rhs")
    val typ = smt.ArrayType(List(index.typ), rhs.typ)
    val st = store(smt.Symbol(lhs, typ), index, rhs)
    onAssign(lhs, st)
    if(!isIO(lhs)) {
      connections(lhs) = connections(lhs) ++ Seq((pathCondition, st))
    }
  }

  private def onConnect(lhs: ir.Expression, rhs: ir.Expression): Unit = lhs match {
    case ir.Reference(name, tpe) => onConnect(name, onExpr(rhs, getWidth(tpe)))
    case firrtl.WRef(name, tpe, _, _) => onConnect(name, onExpr(rhs, getWidth(tpe)))
    case sub : ir.SubField => onConnect(sub.expr.serialize, onExpr(rhs, getWidth(sub.tpe)))
    case sub : firrtl.WSubField => onConnect(sub.expr.serialize, onExpr(rhs, getWidth(sub.tpe)))
    case sub : ir.SubIndex => onConnect(sub.expr.serialize, sub.value, onExpr(rhs, getWidth(sub.tpe)))
    case sub : firrtl.WSubIndex => onConnect(sub.expr.serialize, sub.value, onExpr(rhs, getWidth(sub.tpe)))
    case sub : ir.SubAccess => onConnect(sub.expr.serialize, onExpr(sub.index), onExpr(rhs, getWidth(sub.tpe)))
    case sub : firrtl.WSubAccess => onConnect(sub.expr.serialize, onExpr(sub.index), onExpr(rhs, getWidth(sub.tpe)))
    case other => throw new NotImplementedError(s"TODO: connect to $other")
  }

  def onStmt(s: ir.Statement): Unit = s match {
    case ir.DefWire(_, name, tpe) => defWire(name, tpe)
    case ir.DefRegister(_, name, tpe, _, _, _) => defReg(name, tpe)
    case _ : ir.DefInstance =>
      throw new NotImplementedError("TODO: handle instances")
    case ir.DefMemory(_, name, tpe, depth, _,  _, _,_,_,_) => defMem(name, tpe, depth)
    case ir.DefNode(_, name, value) =>
      defNode(name, onExpr(value))
    case ir.Conditionally(_, cond, tru, fals) =>
      onWhen(onExpr(cond), tru, fals)
    case ir.Block(stmts) =>
      stmts.foreach(onStmt)
    case _ : ir.PartialConnect =>
      throw new RuntimeException("Partial connects are not supported!")
    case ir.Connect(_, loc, expr) =>
      onConnect(loc, expr)
    case ir.IsInvalid(_, expr) =>
      throw new RuntimeException("TODO: deal with invalids")
      //refs(expr.serialize) = getInvalid(getWidth(expr.tpe))
    case ir.EmptyStmt =>
    case other =>
      throw new RuntimeException(s"Unsupported statement: $other")
  }

  private def isInput(p: ir.Port) = p.direction match {
    case ir.Input => true case ir.Output => false
  }
  private def isBundleType(p: ir.Port) = p.tpe.isInstanceOf[ir.BundleType]

  def onPort(p: ir.Port): Unit = {
    if(isBundleType(p)) {
      val typ = p.tpe.asInstanceOf[ir.BundleType]
      typ.fields.foreach { ff =>
        println(s"TODO: $p $ff")
      }
      throw new NotImplementedError("We don't deal with bundles here, use the LowerTypes pass to get rid of them.")
    } else {
      val tpe = onType(p.tpe)
      refs(p.name) = smt.Symbol(p.name, tpe)
      if(isInput(p)) inputs(p.name) = tpe else outputs(p.name) = tpe
    }
  }

  def onModule(m: ir.Module): Unit = {
    m.ports.foreach(onPort)
    onStmt(m.body)
  }
}

trait HasAnnos { val annos: Seq[Annotation] }

/** FirrtlInterpreter with some protocol specific extensions */
class PasoFirrtlInterpreter(circuit: ir.Circuit, val annos: Seq[Annotation]) extends FirrtlInterpreter with HasAnnos {
  require(circuit.modules.length == 1)
  require(circuit.modules.head.isInstanceOf[ir.Module])
  val mod = circuit.modules.head.asInstanceOf[ir.Module]
  private val asserts = annos.collect{ case AssertAnnotation(target) => target.ref }.toSet

  def run(): this.type = { onModule(mod) ; this }

  def onAssert(expr: smt.Expr): Unit = {}

  override def onConnect(lhs: String, rhs: smt.Expr): Unit = {
    if(asserts.contains(lhs)) onAssert(rhs)
    super.onConnect(lhs, rhs)
  }
}
