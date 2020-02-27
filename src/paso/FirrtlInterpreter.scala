package paso

import chisel3.util.log2Ceil
import firrtl.ir
import firrtl.ir.BundleType
import uclid.smt

import scala.collection.mutable

trait SmtHelpers {
  def app(op: smt.Operator, exprs: smt.Expr*) = smt.OperatorApplication(op, exprs.toList)
  def select(array: smt.Expr, index: smt.Expr) = smt.ArraySelectOperation(array, List(index))
  def select(array: smt.Expr, index: BigInt) = {
    require(array.typ.isArray)
    require(array.typ.asInstanceOf[smt.ArrayType].inTypes.length == 1)
    require(array.typ.asInstanceOf[smt.ArrayType].inTypes.head.isBitVector)
    val width = array.typ.asInstanceOf[smt.ArrayType].inTypes.head.asInstanceOf[smt.BitVectorType].width
    smt.ArraySelectOperation(array, List(smt.BitVectorLit(index, width)))
  }
  def store(array: smt.Expr, index: smt.Expr, value: smt.Expr) = smt.ArrayStoreOperation(array, List(index), value)
  def ext(expr: smt.Expr, width: Int, op: (Int, Int) => smt.Operator) = {
    require(expr.typ.isBitVector)
    val w = expr.typ.asInstanceOf[smt.BitVectorType].width
    val e = width - w
    require(e >= 0)
    if(e == 0) expr else app(op(w, e), expr)
  }
  def zext(expr: smt.Expr, width: Int) = ext(expr, width, (w, e) => smt.BVZeroExtOp(w, e))
  def sext(expr: smt.Expr, width: Int) = ext(expr, width, (w, e) => smt.BVSignExtOp(w, e))
  def ite(cond: smt.Expr, tru: smt.Expr, fals: smt.Expr): smt.Expr = app(smt.ITEOp, cond, tru, fals)
}

object FirrtlInterpreter {
  def run(stmt: ir.Statement): Unit = new FirrtlInterpreter().onStmt(stmt)
  def run(m: ir.Module): Unit = new FirrtlInterpreter().onModule(m)
}

class FirrtlInterpreter extends SmtHelpers {
  val refs = mutable.HashMap[String, smt.Expr]()

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
  private def getBitVecType(width: BigInt): smt.Type = {
    require(width > 0, "Zero width wires are not supported")
    if(width == 1) smt.BoolType else smt.BitVectorType(width.toInt)
  }

  def onType(t: ir.Type): smt.Type = t match {
    case ir.UIntType(ir.IntWidth(w)) => getBitVecType(w)
    case ir.SIntType(ir.IntWidth(w)) => getBitVecType(w)
    case ir.ResetType => smt.BoolType
    case ir.ClockType => smt.BoolType
    case ir.VectorType(tpe, size) => smt.ArrayType(List(getBitVecType(log2Ceil(size))), onType(tpe))
    case other => throw new NotImplementedError(s"TODO: implement conversion for $other")
  }

  // most important to customize
  def onReference(r: ir.Reference): smt.Expr = refs(r.name)
  def onSubfield(r: ir.SubField): smt.Expr = refs(r.serialize)
  def getInvalid(width: Int): smt.Expr = if(width == 1) smt.BooleanLit(false) else smt.BitVectorLit(0, width)
  def defWire(name: String, tpe: ir.Type): Unit = {
    require(!refs.contains(name))
    refs(name) = smt.Symbol(name, onType(tpe))
  }
  def defNode(name: String, value: smt.Expr): Unit = {
    require(!refs.contains(name))
    refs(name) = value
  }
  def onWhen(cond: smt.Expr, tru: ir.Statement, fals: ir.Statement): Unit = ???

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

  def onExpr(e: ir.Expression): smt.Expr = e match {
    case r: ir.Reference =>
      onReference(r)
    case r: ir.SubField =>
      onSubfield(r)
    case ir.SubIndex(expr, value, _) =>
      select(onExpr(expr), value)
    // TODO: handle out of bounds accesses gracefully
    case ir.SubAccess(expr, index, tpe) =>
      val array = onExpr(expr)
      val indexWidth = array.typ.asInstanceOf[smt.ArrayType].inTypes.head.asInstanceOf[smt.BitVectorType].width
      select(onExpr(expr), onExpr(index, indexWidth))
    case ir.Mux(cond, tval, fval, _) =>
      val args = onExpr(tval, fval)
      ite(onExpr(cond, 1), args._1, args._2)
    case ir.ValidIf(cond, value, tpe) =>
      val sv = onExpr(value)
      ite(onExpr(cond, 1), sv, getInvalid(getWidth(sv.typ)))
    case ir.UIntLiteral(value, width) =>
      smt.BitVectorLit(value, getWidth(width))
    case ir.SIntLiteral(value, width) =>
      smt.BitVectorLit(value, getWidth(width))
    case ir.DoPrim(op, args, consts, tpe) =>
      throw new NotImplementedError(s"TODO: DoPrim($op, $args, $consts, $tpe)")
    case _ : ir.FixedLiteral =>
      throw new NotImplementedError("TODO: fixed point support")
    case other =>
      throw new NotImplementedError(s"TODO: implement $other")
  }

  def onConnect(lhs: String, rhs: smt.Expr): Unit = {
    println(s"$lhs := $rhs")
  }
  def onConnect(lhs: String, index: Int, rhs: smt.Expr): Unit = {
    println(s"$lhs[$index] := $rhs")
  }

  private def onConnect(lhs: ir.Expression, rhs: ir.Expression): Unit = lhs match {
    case ir.Reference(name, tpe) => onConnect(name, onExpr(rhs, getWidth(tpe)))
    case sub : ir.SubField => onConnect(sub.serialize, onExpr(rhs, getWidth(sub.tpe)))
    case sub : ir.SubIndex => onConnect(sub.serialize, sub.value, onExpr(rhs, getWidth(sub.tpe)))
    case other => throw new NotImplementedError(s"TODO: connect to $other")
  }

  def onStmt(s: ir.Statement): Unit = s match {
    case ir.DefWire(_, name, tpe) =>
      defWire(name, tpe)
    case _ : ir.DefRegister =>
      throw new NotImplementedError("TODO: handle registers")
    case _ : ir.DefInstance =>
      throw new NotImplementedError("TODO: handle instances")
    case _: ir.DefMemory =>
      throw new NotImplementedError("TODO: handle memories")
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
      refs(expr.serialize) = getInvalid(getWidth(expr.tpe))
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
      // TODO: support nested bundles
      typ.fields.foreach { ff =>
        println(s"TODO: $p $ff")
      }
    } else {
      if(isInput(p)) {
        refs(p.name) = smt.Symbol(p.name, onType(p.tpe))
      } else { /* ignoring outputs */}
    }
  }

  def onModule(m: ir.Module): Unit = {
    m.ports.foreach(onPort)
    onStmt(m.body)
  }
}
