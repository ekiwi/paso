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

class FirrtlInterpreter extends SMTHelpers {
  case class Value(e: smt.Expr, valid: smt.Expr = tru) {
    def isValid: Boolean = valid == tru
    def map(foo: smt.Expr => smt.Expr): Value = copy(e = foo(e))
    def get: smt.Expr = { assert(isValid, s"expected value that was trivially valid, not: validif($valid, $e)") ; e}
    def typ: smt.Type = e.typ
  }
  val refs = mutable.HashMap[String, Value]()
  val connections = mutable.HashMap[String, Seq[(smt.Expr, Value)]]()
  val inputs = mutable.HashMap[String, smt.Type]()
  val outputs = mutable.HashMap[String, smt.Type]()
  val regs = mutable.HashMap[String, smt.Type]()
  case class Mem(name: String, typ: smt.Type, readers: Seq[String], writers: Seq[String])
  val mems = mutable.HashMap[String, Mem]()
  val wires = mutable.HashMap[String, smt.Type]()
  protected val cond_stack = mutable.Stack[smt.Expr]()
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
    case ir.ClockType => 1
    case ir.ResetType => 1
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
  def onAssign(name: String, expr: Value): Unit = {}
  def onReference(r: ir.Reference): Value = refs(r.name)
  def onSubfield(r: ir.SubField): Value = refs(r.serialize)
  def onSubAccess(array: Value, index: ir.Expression): Value= {
    val indexWidth = array.get.typ.asInstanceOf[smt.ArrayType].inTypes.head.asInstanceOf[smt.BitVectorType].width
    val ii = onExpr(index, indexWidth)
    Value(select(array.get, ii.get))
  }
  private def defX(name: String, tpe: smt.Type, registry: Option[mutable.HashMap[String, smt.Type]]): Unit = {
    require(!refs.contains(name))
    refs(name) = Value(smt.Symbol(name, tpe))
    connections(name) = Seq()
    registry.foreach(r => r(name) = tpe)
  }
  def defWire(name: String, tpe: ir.Type): Unit = defX(name, onType(tpe), Some(wires))
  def defReg(name: String, tpe: ir.Type): Unit = defX(name, onType(tpe), Some(regs))
  def defMem(m: ir.DefMemory): Unit = {
    val addrWidth = log2Ceil(m.depth)
    val isPowerOf2 = BigInt(1) << addrWidth == m.depth
    assert(isPowerOf2)
    assert(m.readLatency == 0, "Please use Mem(...)")
    assert(m.writeLatency == 1, "Please use Mem(...)")
    assert(m.readwriters.isEmpty, "TODO: maybe deal with read and write port")
    val dataType = onType(m.dataType)
    val addrType = smt.BitVectorType(addrWidth)
    m.readers.foreach { r =>
      defX(m.name + "." + r + ".data", dataType, None)
      defX(m.name + "." + r + ".addr", addrType, None)
      defX(m.name + "." + r + ".en", smt.BoolType, None)
      defX(m.name + "." + r + ".clk", smt.BoolType, None)
    }
    m.writers.foreach { w =>
      defX(m.name + "." + w + ".data", dataType, None)
      defX(m.name + "." + w + ".addr", addrType, None)
      defX(m.name + "." + w + ".en", smt.BoolType, None)
      defX(m.name + "." + w + ".clk", smt.BoolType, None)
      defX(m.name + "." + w + ".mask", smt.BoolType, None)
    }
    val typ = smt.ArrayType(List(addrType), dataType)
    defX(m.name, typ, None)
    mems(m.name) = Mem(m.name, typ, m.readers, m.writers)
  }
  def getSimplifiedFinalValue(signal: String): Option[Value] = {
    val cons = connections.getOrElse(signal, refs.get(signal).map { r => Seq((tru, r)) }.getOrElse(return None))
    assert(cons.nonEmpty, s"No connections to $signal")
    assert(cons.length == 1, "TODO: support multiple connections (remember last connect semantics)")
    assert(cons.head._1 == tru, "TODO: support path conditions other than true")
    Some(cons.head._2.map(SMTSimplifier.simplify))
  }
  def getMemReadExpressions(): Map[smt.Expr, smt.Expr] = {
    mems.values.flatMap { m =>
      val mem = smt.Symbol(m.name, m.typ)
      // check read ports to make sure they are enabled
      m.readers.map { r =>
        val dataSym: smt.Expr = smt.Symbol(m.name + "." + r + ".data", m.typ.asInstanceOf[smt.ArrayType].outType)
        val addr = getSimplifiedFinalValue(m.name + "." + r + ".addr").get
        val en = getSimplifiedFinalValue(m.name + "." + r + ".en").get
        // assert(en.get == tru, s"Currently we require reads to always be enabled! ${en.get}")
        if(en.get != tru) println(s"WARN: ${dataSym} might not always be enabled.")
        if(!addr.isValid) println(s"WARN: ${dataSym} address might not always be enabled.")
        dataSym -> select(mem, addr.e)
      }
    }.toMap
  }
  def getMemUpdates(name: String): smt.Expr = {
    assert(mems.contains(name))
    val m = mems(name)

    // generate updates from write ports
    val writes = m.writers.map { w =>
      val data = getSimplifiedFinalValue(m.name + "." + w + ".data").get
      val addr = getSimplifiedFinalValue(m.name + "." + w + ".addr").get
      val en = getSimplifiedFinalValue(m.name + "." + w + ".en").get.get
      val enSimpl = SMTSimplifier.simplify(en)
      val mask = getSimplifiedFinalValue(m.name + "." + w + ".mask").get
      // it is ok for data, addr and mask to be invalid when the write port is not enabled
      def validWhenEnabled(v: Value) ={
        val valid = SMTSimplifier.simplify(v.valid)
        valid == tru || valid == enSimpl
      }
      assert(validWhenEnabled(mask))
      assert(validWhenEnabled(addr))
      assert(validWhenEnabled(data))
      assert(mask.e == tru, "Currently we require the write mask to always be true!")
      (enSimpl, addr.e, data.e)
    }

    //assert(writes.length < 2, "TODO: deal with write-write conflicts")
    if(writes.length >= 2) println("WARN: TODO: deal with write-write conflicts")
    writes.foldLeft[smt.Expr](smt.Symbol(m.name, m.typ)) { case (mem, (en, addr, data)) =>
      val update = store(mem, addr, data)
      if(en == tru) update else ite(en, update, mem)
    }
  }

  def defNode(name: String, value: Value): Unit = {
    onAssign(name, value)
    require(!refs.contains(name))
    refs(name) = value
  }
  def onWhen(cond: Value, tru: ir.Statement, fals: ir.Statement): Unit = {
    cond_stack.push(cond.get)
    onStmt(tru)
    cond_stack.pop()
    cond_stack.push(app(smt.NegationOp, cond.get))
    onStmt(fals)
    cond_stack.pop()
  }

  // extends expression to width
  def onExpr(e: ir.Expression, width: Int): Value =
    if(isSigned(e.tpe)) onExpr(e).map(sext(_, width)) else onExpr(e).map(zext(_, width))

  // extends expressions to be the same length
  def onExpr(e1: ir.Expression, e2: ir.Expression): Tuple2[Value, Value] = {
    require(isSigned(e1.tpe) == isSigned(e2.tpe), s"$e1 : ${e1.tpe} vs $e2 : ${e2.tpe}")
    val (s1, s2) = (onExpr(e1), onExpr(e2))
    val width = Seq(getWidth(s1.typ), getWidth(s2.typ)).max
    if(isSigned(e1.tpe)) (s1.map(sext(_, width)), s2.map(sext(_, width)))
    else (s1.map(zext(_, width)), s2.map(zext(_, width)))
  }

  private def onLiteral(value: BigInt, width: Int): smt.Expr = {
    require(width > 0, "Zero width wires are not supported")
    if(width == 1) smt.BooleanLit(value != 0) else smt.BitVectorLit(value, width)
  }

  def onExpr(e: ir.Expression): Value = e match {
    case r: ir.Reference => onReference(r)
    case r: ir.SubField => onSubfield(r)
    case ir.SubIndex(expr, value, _, _) => onExpr(expr).map(select(_, value))
    // TODO: handle out of bounds accesses gracefully
    case ir.SubAccess(expr, index, tpe, _) => onSubAccess(onExpr(expr), index)
    case ir.Mux(c, tval, fval, _) =>
      val args = onExpr(tval, fval)
      val cond = onExpr(c, 1).get
      // shannon expansion
      val valid = SMTSimplifier.simplify(or(and(cond, args._1.valid), and(not(cond), args._2.valid)))
      val e = ite(cond, args._1.e, args._2.e)
      Value(e, valid)
    case ir.ValidIf(cond, value, tpe) =>
      val e = onExpr(value)
      val valid = and(e.valid, onExpr(cond).get)
      e.copy(valid = valid)
    case ir.UIntLiteral(value, width) => Value(onLiteral(value, getWidth(width)))
    case ir.SIntLiteral(value, width) => Value(onLiteral(value, getWidth(width)))
    case ir.DoPrim(op, Seq(a, b), Seq(), tpe) =>
      Value(BinOpCompiler.compile(op, a.tpe, b.tpe, tpe)._2(onExpr(a).get, onExpr(b).get))
    case ir.DoPrim(op, Seq(a), consts, tpe) =>
      Value(UnOpCompiler.compile(op, a.tpe, tpe, consts)._2(onExpr(a).get))
    case ir.DoPrim(op, args, consts, tpe) =>
      throw new NotImplementedError(s"TODO: DoPrim($op, $args, $consts, $tpe)")
    case _ : ir.FixedLiteral =>
      throw new NotImplementedError("TODO: fixed point support")
    case other =>
      throw new NotImplementedError(s"TODO: implement $other")
  }

  def onConnect(lhs: String, rhs: Value): Unit = {
    onAssign(lhs, rhs)
    if(!isInput(lhs)) {
      connections(lhs) = connections(lhs) ++ Seq((pathCondition, rhs))
    }
  }
  def onConnect(lhs: String, index: Int, rhs: Value): Unit = {
    //println(s"$lhs[$index] := $rhs")
    val st = Value(store(smt.Symbol(lhs, rhs.typ), index, rhs.get))
    onAssign(lhs, st)
    if(!isInput(lhs)) {
      connections(lhs) = connections(lhs) ++ Seq((pathCondition, st))
    }
  }
  def onConnect(lhs: String, index: Value, rhs: Value): Unit = {
    //println(s"$lhs[$index] := $rhs")
    val typ = smt.ArrayType(List(index.typ), rhs.typ)
    val st = Value(store(smt.Symbol(lhs, typ), index.get, rhs.get))
    onAssign(lhs, st)
    if(!isInput(lhs)) {
      connections(lhs) = connections(lhs) ++ Seq((pathCondition, st))
    }
  }

  private def onConnect(lhs: ir.Expression, rhs: ir.Expression): Unit = lhs match {
    case ir.Reference(name, tpe, _, _) => onConnect(name, onExpr(rhs, getWidth(tpe)))
    case sub : ir.SubField => onConnect(sub.serialize, onExpr(rhs, getWidth(sub.tpe)))
    case sub : ir.SubIndex => onConnect(sub.expr.serialize, sub.value, onExpr(rhs, getWidth(sub.tpe)))
    case sub : ir.SubAccess => onConnect(sub.expr.serialize, onExpr(sub.index), onExpr(rhs, getWidth(sub.tpe)))
    case other => throw new NotImplementedError(s"TODO: connect to $other")
  }

  def onStmt(s: ir.Statement): Unit = s match {
    case ir.DefWire(_, name, tpe) => defWire(name, tpe)
    case ir.DefRegister(_, name, tpe, _, _, _) => defReg(name, tpe)
    case _ : ir.DefInstance =>
      throw new NotImplementedError("TODO: handle instances")
    case m : ir.DefMemory => defMem(m)
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
      onConnect(expr, ir.ValidIf(ir.UIntLiteral(0), ir.UIntLiteral(0), expr.tpe))
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
      if(isInput(p)) {
        defX(p.name, tpe, Some(inputs))
      }  else {
        defX(p.name, tpe, Some(outputs))
      }
    }
  }

  def onEnterBody(): Unit = {}

  def onModule(m: ir.Module): Unit = {
    m.ports.foreach(onPort)
    onEnterBody()
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

  def onAssert(expr: Value): Unit = {}

  override def onConnect(lhs: String, rhs: Value): Unit = {
    if(asserts.contains(lhs)) onAssert(rhs)
    super.onConnect(lhs, rhs)
  }
}
