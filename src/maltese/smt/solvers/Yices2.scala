// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.smt.solvers

import maltese.smt._
import scala.collection.mutable


object Yices2 {
  def apply(logic: Solver.Logic = QF_ABV): Yices2 = {
    val lib = Yices2Api.lib
    val conf = assertNoError(lib.yices_new_config())
    val ctx = assertNoError(lib.yices_new_context(conf))
    val params = assertNoError(lib.yices_new_param_record())
    val y = new Yices2(lib, conf, ctx, params)
    y.setLogic(logic)
    y
  }
  private def assertNoError[T](v: T): T = { Yices2Api.assertNoError() ; v }
  private def bitArrayToBigInt(a: Array[Int]): BigInt = BigInt(a.reverseIterator.map(_.toString).mkString(""), 2)
}

class Yices2 private(lib: Yices2Api, conf: Yices2Api.ConfigT, ctx: Yices2Api.ContextT, params: Yices2Api.ParamsT) extends Solver {
  override def name = "yices2"
  override def supportsQuantifiers = false
  override def supportsConstArrays = false
  override def supportsUninterpretedFunctions = true

  import Yices2.{assertNoError, bitArrayToBigInt}

  private var _stackDepth: Int = 0
  override def stackDepth = _stackDepth
  override def push(): Unit = { assertNoError(lib.yices_push(ctx)) ;  _stackDepth += 1 }
  override def pop(): Unit = { assertNoError(lib.yices_pop(ctx)) ;  _stackDepth -= 1 }
  override def assert(expr: BVExpr): Unit = assertNoError(lib.yices_assert_formula(ctx, convert(expr)))
  override def queryModel(e: BVSymbol): Option[BigInt] = model match {
    case None => None
    case Some(m) => symbols.get(e.name).map { info =>
      require(info.sym.isInstanceOf[BVSymbol])
      require(info.sym.asInstanceOf[BVSymbol].width == e.width)
      val valueArray = new Array[Int](e.width)
      assertNoError(lib.yices_get_bv_value(m, info.term, valueArray))
      bitArrayToBigInt(valueArray)
    }
  }

  // TODO
  override def getValue(e: BVExpr) = ???
  override def getValue(e: ArrayExpr) = ???

  override def runCommand(cmd: SMTCommand): Unit = cmd match {
    case Comment(_) => // ignore
    case SetLogic(logic) => setLogic(logic)
    case DefineFunction(name, args, e) => ???
    case DeclareFunction(sym, args) => ???
    case DeclareUninterpretedSort(name) => ???
    case DeclareUninterpretedSymbol(name, tpe) => ???
  }

  /** releases all native resources */
  override def close(): Unit = {
    freeModel()
    symbols.clear()
    assertNoError(lib.yices_free_param_record(params))
    assertNoError(lib.yices_free_context(ctx))
  }

  // keep track of symbols:
  private case class SymbolInfo(sym: SMTSymbol, term: Yices2Api.TermT)
  private val symbols = new mutable.HashMap[String, SymbolInfo]
  private var model: Option[Yices2Api.ModelT] = None

  override protected def doSetLogic(logic: Solver.Logic): Unit = {
    // TODO: is there a way to construct a solver for a particular logic?
    //lib.yices_default_config_for_logic(conf, "QF_AUFBV")
  }
  override protected def doCheck(produceModel: Boolean): SolverResult = {
    freeModel()
    assertNoError(lib.yices_check_context(ctx, params)) match {
      case Yices2Api.STATUS_IDLE => throw new RuntimeException("Unexpected yices return: STATUS_IDLE")
      case Yices2Api.STATUS_SEARCHING => throw new RuntimeException("Unexpected yices return: STATUS_SEARCHING")
      case Yices2Api.STATUS_INTERRUPTED => throw new RuntimeException("Unexpected yices return: STATUS_INTERRUPTED")
      case Yices2Api.STATUS_ERROR => throw new RuntimeException("Unexpected yices return: STATUS_ERROR")
      case Yices2Api.STATUS_SAT =>
        model = Some(assertNoError(lib.yices_get_model(ctx, 0)))
        IsSat
      case Yices2Api.STATUS_UNSAT => IsUnSat
      case Yices2Api.STATUS_UNKNOWN => IsUnknown
    }
  }
  private def freeModel(): Unit = model match {
    case Some(m) =>
      assertNoError(lib.yices_free_model(m))
      model = None
    case None =>
  }

  // translate expressions
  private def convert(expr: BVExpr): Yices2Api.TermT = expr match {
    // nullary
    case s: BVSymbol => symbol2Yices(s)
    case BVLiteral(value, 1) =>
      assertNoError(if(value == 1) lib.yices_true() else lib.yices_false())
    case BVLiteral(value, width) =>
      assertNoError(
        if(width < 64) lib.yices_bvconst_int64(width, value.toLong)
        else lib.yices_parse_bvbin(value.toString(2))
      )

    // unary
    case BVExtend(e, 0, _) => convert(e)
    case BVExtend(e, by, true) =>
      assertNoError(lib.yices_sign_extend(convertToBV(e), by))
    case BVExtend(e, by, false) =>
      assertNoError(lib.yices_zero_extend(convertToBV(e), by))
    case BVSlice(e, hi, lo) if lo == 0 && (hi - 1) == e.width => convert(e)
    case BVSlice(e, hi, lo) =>
      val r = assertNoError(lib.yices_bvextract(convert(e), lo, hi))
      if(lo == hi) { toBool(r) } else { r }
    case BVNot(e) if e.width == 1 =>
      assertNoError(lib.yices_not(convert(e)))
    case BVNot(e) =>
      assertNoError(lib.yices_bvnot(convert(e)))
    case BVNegate(e) =>
      assertNoError(lib.yices_bvneg(convertToBV(e)))

    // binary
    case BVEqual(a, b) if a.width == 1 =>
      assertNoError(lib.yices_iff(convert(a), convert(b)))
    case BVEqual(a, b) =>
      assertNoError(lib.yices_eq(convert(a), convert(b)))
    case ArrayEqual(a, b) =>
      throw new NotImplementedError("TODO: array support")
    case BVComparison(Compare.Greater, a, b, true) =>
      assertNoError(lib.yices_bvsgt_atom(convertToBV(a), convertToBV(b)))
    case BVComparison(Compare.GreaterEqual, a, b, true) =>
      assertNoError(lib.yices_bvsge_atom(convertToBV(a), convertToBV(b)))
    case BVComparison(Compare.Greater, a, b, false) =>
      assertNoError(lib.yices_bvgt_atom(convertToBV(a), convertToBV(b)))
    case BVComparison(Compare.GreaterEqual, a, b, false) =>
      assertNoError(lib.yices_bvge_atom(convertToBV(a), convertToBV(b)))
    case BVOp(Op.And, a, b) if a.width == 1 =>
      assertNoError(lib.yices_and2(convert(a), convert(b)))
    case BVOp(Op.Or, a, b) if a.width == 1 =>
      assertNoError(lib.yices_or2(convert(a), convert(b)))
    case BVOp(Op.Xor, a, b) if a.width == 1 =>
      assertNoError(lib.yices_xor2(convert(a), convert(b)))
    case BVOp(op, a, b) =>
      val (nA, nB) = (convertToBV(a), convertToBV(b))
      val r = assertNoError(op match {
        case maltese.smt.Op.And => lib.yices_bvand2(nA, nB)
        case maltese.smt.Op.Or => lib.yices_bvor2(nA, nB)
        case maltese.smt.Op.Xor => lib.yices_bvxor2(nA, nB)
        case maltese.smt.Op.ShiftLeft => lib.yices_bvshl(nA, nB)
        case maltese.smt.Op.ArithmeticShiftRight => lib.yices_bvashr(nA, nB)
        case maltese.smt.Op.ShiftRight => lib.yices_bvlshr(nA, nB)
        case maltese.smt.Op.Add => lib.yices_bvadd(nA, nB)
        case maltese.smt.Op.Mul => lib.yices_bvmul(nA, nB)
        case maltese.smt.Op.SignedDiv =>lib.yices_bvsdiv(nA, nB)
        case maltese.smt.Op.UnsignedDiv =>lib.yices_bvdiv(nA, nB)
        case maltese.smt.Op.SignedMod =>lib.yices_bvsmod(nA, nB)
        case maltese.smt.Op.SignedRem =>lib.yices_bvsrem(nA, nB)
        case maltese.smt.Op.UnsignedRem =>lib.yices_bvrem(nA, nB)
        case maltese.smt.Op.Sub =>lib.yices_bvsub(nA, nB)
      })
      if(a.width == 1) { toBool(r) } else { r }
    case BVConcat(a, b) =>
      assertNoError(lib.yices_bvconcat2(convertToBV(a), convertToBV(b)))
    case BVImplies(a, b) =>
      assertNoError(lib.yices_implies(convert(a), convert(b)))
    case ArrayRead(a, b) =>
      throw new NotImplementedError("TODO: support array expressions")
    // ternary
    case BVIte(cond, tru, fals) =>
      assertNoError(lib.yices_ite(convert(cond), convert(tru), convert(fals)))
    // n-ary
    case BVSelect(_) =>
      throw new NotImplementedError("BVSelect")
  }

  /** ensures that the result will be a bit vector */
  private def convertToBV(expr: BVExpr): Yices2Api.TermT =
    if(expr.width == 1) { toBitVector(convert(expr)) } else { convert(expr) }

  private def toBool(t: Yices2Api.TermT): Yices2Api.TermT = {
    val one = assertNoError(lib.yices_bvconst_int32(1, 1))
    assertNoError(lib.yices_eq(t, one))
  }

  private def toBitVector(t: Yices2Api.TermT): Yices2Api.TermT = {
    val one = assertNoError(lib.yices_bvconst_int32(1, 1))
    val zero = assertNoError(lib.yices_bvconst_int32(1, 0))
    assertNoError(lib.yices_ite(t, one, zero))
  }

  private def symbol2Yices(s: SMTSymbol): Yices2Api.TermT = {
    symbols.get(s.name) match {
      case Some(info) => require(info.sym == s) ; info.term
      case None => {
        val typ = typ2Yices(s)
        val term = assertNoError(lib.yices_new_uninterpreted_term(typ))
        symbols(s.name) = SymbolInfo(s, term)
        term
      }
    }
  }

  private def bvType(width: Int): Yices2Api.TypeT =
    assertNoError(if(width == 1) lib.yices_bool_type() else lib.yices_bv_type(width))

  private def typ2Yices(e: SMTExpr): Yices2Api.TypeT = e match {
    case b: BVExpr => bvType(b.width)
    case a: ArrayExpr =>
      val index = bvType(a.indexWidth)
      val data = bvType(a.dataWidth)
      lib.yices_function_type(1, Array(index), data)
  }


}
