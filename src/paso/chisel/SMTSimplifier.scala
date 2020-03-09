// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel

import uclid.smt._
import scala.collection.mutable
import scala.BigInt

/**
 * Walks a SMT formula and tries to simplify it.
 *
 * Many of the simplifications used are inspired by the awesome PySMT library (https://github.com/pysmt)
 */
class SMTSimplifier private() {
  private val simplified: mutable.HashMap[Expr, Expr] = mutable.HashMap()

  // "apply"
  protected def app(op: Operator, args: List[Expr]): Expr =
    OperatorApplication(op, args)

  protected def bitWidth(e: Expr): Int = e.typ.asInstanceOf[BitVectorType].width

  // ITE Simplification
  protected def simplifyITE(cond: Expr, a: Expr, b: Expr): Expr = {
    cond match {
      case BooleanLit(sel) => if(sel) a else b
      case _ => if(a == b) { a } else { app(ITEOp, List(cond, a, b)) }
    }
  }

  // Boolean Simplification
  protected def simplifyBoolBinOp(op: BoolResultOp, a1: Expr, a2: Expr): Expr = op match {
    case IffOp => (a1, a2) match {
      case (BooleanLit(true), e2) => e2
      case (BooleanLit(false), e2) => app(NegationOp, List(e2))
      case (e1, BooleanLit(true)) => e1
      case (e1, BooleanLit(false)) => app(NegationOp, List(e1))
      case (e1, e2) => if(e1 == e2) BooleanLit(true) else app(op, List(e1, e2))
    }
    case ImplicationOp => (a1, a2) match {
      case (BooleanLit(true), e2) => e2
      case (BooleanLit(false), _) => BooleanLit(true)
      case (_, BooleanLit(true)) => BooleanLit(true)
      case (e1, BooleanLit(false)) => app(NegationOp, List(e1))
      case (OperatorApplication(NegationOp, List(n)), p) if n == p => n
      case (p, OperatorApplication(NegationOp, List(n))) if n == p => app(NegationOp, List(n))
      case (e1, e2) => if(e1 == e2) BooleanLit(true) else app(op, List(e1, e2))
    }
    case ConjunctionOp => (a1, a2) match {
      case (BooleanLit(true), e2) => e2
      case (BooleanLit(false), _) => BooleanLit(false)
      case (e1, BooleanLit(true)) => e1
      case (_, BooleanLit(false)) => BooleanLit(false)
      case (OperatorApplication(NegationOp, List(n)), p) if n == p => BooleanLit(false)
      case (p, OperatorApplication(NegationOp, List(n))) if n == p => BooleanLit(false)
      case (e1, e2) => if(e1 == e2) e1 else app(op, List(e1, e2))
    }
    case DisjunctionOp => (a1, a2) match {
      case (BooleanLit(true), _) => BooleanLit(true)
      case (BooleanLit(false), e2) => e2
      case (_, BooleanLit(true)) => BooleanLit(true)
      case (e1, BooleanLit(false)) => e1
      case (OperatorApplication(NegationOp, List(n)), p) if n == p => BooleanLit(true)
      case (p, OperatorApplication(NegationOp, List(n))) if n == p => BooleanLit(true)
      case (e1, e2) => if(e1 == e2) e1 else app(op, List(e1, e2))
    }
  }

  protected def simplifyNegationOp(arg: Expr): Expr = arg match {
    case BooleanLit(b) => BooleanLit(!b)
    case OperatorApplication(NegationOp, inner) => inner.head
    case OperatorApplication(InequalityOp, inner) => app(EqualityOp, inner)
    case other => app(NegationOp, List(other))
  }

  // Simplify Equality
  protected def simplifyEquals(a1: Expr, a2: Expr): Expr = {
    if(a1.typ.isBool) {
      simplifyBoolBinOp(IffOp, a1, a2)
    } else {
      (a1, a2) match {
        case (BitVectorLit(e1, _), BitVectorLit(e2, _)) => BooleanLit(e1 == e2)
        case (IntLit(e1), IntLit(e2)) => BooleanLit(e1 == e2)
        case (e1, e2) => if (e1 == e2) BooleanLit(true) else app(EqualityOp, List(a1, a2))
      }
    }
  }

  protected def simplifyInequality(args: List[Expr]): Expr = simplify(app(NegationOp, List(app(EqualityOp, args))))

  // Simplify BitVector
  // TODO: simplify BV comparison
  protected def simplifyBVCmp(op: BoolResultOp, a1: Expr, a2: Expr): Expr = app(op, List(a1, a2))

  protected def simplifyBVOp(op: BVResultOp, args: List[Expr]): Expr = (op, args) match {
    case (BVZeroExtOp(_, e), List(BitVectorLit(value, width))) => BitVectorLit(value, width + e)
    case (BVSignExtOp(_, e), List(BitVectorLit(value, width))) => {
      val sign_bit = (value >> (width - 1)) == 1
      val new_value = if(sign_bit) { (((1 << e) - 1) << width) | value } else { value }
      BitVectorLit(new_value, width + e)
    }
    case _ => app(op, args)
  }

  // Simplify Integer
  // TODO: simplify integers
  protected def simplifyIntCmp(op: BoolResultOp, a1: Expr, a2: Expr): Expr = app(op, List(a1, a2))
  protected def simplifyIntOp(op: IntResultOp, args: List[Expr]): Expr = app(op, args)

  // Operator Parsing / Dispatcher
  protected def simplifyBoolResultOp(op: BoolResultOp, args: List[Expr]): Expr = op match {
    case IffOp         => simplifyBoolBinOp(op, args.head, args(1))
    case ImplicationOp => simplifyBoolBinOp(op, args.head, args(1))
    case ConjunctionOp => simplifyBoolBinOp(op, args.head, args(1))
    case DisjunctionOp => simplifyBoolBinOp(op, args.head, args(1))
    case NegationOp    => simplifyNegationOp(args.head)

    case EqualityOp    => simplifyEquals(args.head, args(1))
    case InequalityOp  => simplifyInequality(args)

    case IntLTOp       => simplifyIntCmp(op, args.head, args(1))
    case IntLEOp       => simplifyIntCmp(op, args.head, args(1))
    case IntGTOp       => simplifyIntCmp(op, args.head, args(1))
    case IntGEOp       => simplifyIntCmp(op, args.head, args(1))

    case BVLTOp(_)     => simplifyBVCmp(op, args.head, args(1))
    case BVLEOp(_)     => simplifyBVCmp(op, args.head, args(1))
    case BVGTOp(_)     => simplifyBVCmp(op, args.head, args(1))
    case BVGEOp(_)     => simplifyBVCmp(op, args.head, args(1))
    case BVLTUOp(_)    => simplifyBVCmp(op, args.head, args(1))
    case BVLEUOp(_)    => simplifyBVCmp(op, args.head, args(1))
    case BVGTUOp(_)    => simplifyBVCmp(op, args.head, args(1))
    case BVGEUOp(_)    => simplifyBVCmp(op, args.head, args(1))

    case a: ForallOp   => app(a, args)

    case other => throw new RuntimeException(s"Unexpected BoolenResultOp: $other")
  }

  protected def simplifyOpApp(op: Operator, args: List[Expr]): Expr = op match {
    case o: IntResultOp => simplifyIntOp(o, args)
    case o: BVResultOp => simplifyBVOp(o, args)
    case o: BoolResultOp => simplifyBoolResultOp(o, args)
    case ITEOp => simplifyITE(args.head, args(1), args(2))
    case _ => app(op, args)
  }

  private def simplify(expr: Expr): Expr = {
    val terminal = expr match {
      case _: Literal => true
      case _: Symbol => true
      case _ => false
    }

    if(terminal) { expr } else {
      if(simplified.contains(expr)) { return simplified(expr) }

      val simple = expr match {
        case OperatorApplication(op, args) => simplifyOpApp(op, args.map(simplify))
        case ArraySelectOperation(e, index) =>
          ArraySelectOperation(simplify(e), index.map(simplify))
        case ArrayStoreOperation(e, index, value) =>
          ArrayStoreOperation(simplify(e), index.map(simplify), simplify(value))
        case LetExpression(letBindings, expr) =>
          LetExpression(letBindings.map{ case (sym, e) => (sym, simplify(e))}, simplify(expr))
        case FunctionApplication(e, args) =>
          FunctionApplication(simplify(e), args.map(simplify))
        case Lambda(ids, e) => Lambda(ids, simplify(e))
        case DefineFun(id, args, e) => DefineFun(id, args, simplify(e))
        case other => throw new RuntimeException(s"Unexpected expression: $other")
      }

      simplified(expr) = simple
      simple
    }
  }


  def run(expr: Expr): Expr = {
    simplify(expr)
  }

  /** uses an SMT solver to verify every simplification made with this instance */
  def verifySimplifications(solver: Context): Unit = {
    simplified.foreach { case (expr, simple) =>
      assert(expr.typ == simple.typ, s"type mismatch: $expr vs $simple")
      val eq = OperatorApplication(EqualityOp, List(expr, simple))

      // check validity of equality
      solver.push()
      solver.assert(OperatorApplication(NegationOp, List(eq)))
      val res = solver.check()
      solver.pop()

      assert(res.isFalse, s"$expr != $simple")
    }
  }
}

object SMTSimplifier {
  def apply(): SMTSimplifier = new SMTSimplifier()
  def forFirrtl(): SMTSimplifier = new SMTSimplifier() with FirrtlSymExecSimplifications
  private lazy val simplifier = forFirrtl()
  def simplify(e: Expr): Expr = simplifier.run(e)
}

trait FirrtlSymExecSimplifications extends SMTSimplifier {
  private val BV1 = BitVectorLit(1, 1)
  private val BV0 = BitVectorLit(0, 1)

  override protected def simplifyEquals(a1: Expr, a2: Expr): Expr = {

    (a1, a2) match {
      // toBool(toBV(e)) pattern (ITE(e, 1bv1, 0bv1) == 1bv1) <=> e
      case (OperatorApplication(ITEOp, List(e, BV1, BV0)), BV1) => e
      // make sure that constant comparisons are evaluated
      case (BitVectorLit(e1, _), BitVectorLit(e2, _)) => BooleanLit(e1 == e2)
      // normalize constants to appear on the right
      case (lit @ BitVectorLit(_, _), e) => simplifyCompareToConstant(EqualityOp, e, lit)
      case (e, lit @ BitVectorLit(_, _)) => simplifyCompareToConstant(EqualityOp, e, lit)
      case _ => super.simplifyEquals(a1, a2)
    }
  }

  override protected def simplifyBVCmp(op: BoolResultOp, a1: Expr, a2: Expr): Expr = {
    def swapOp = op match {
      case BVGTUOp(w) => BVLTUOp(w)
      case BVLTUOp(w) => BVGTUOp(w)
      case BVGEUOp(w) => BVLEUOp(w)
      case BVLEUOp(w) => BVGEUOp(w)
      case BVGTOp(w) => BVLTOp(w)
      case BVLTOp(w) => BVGTOp(w)
      case BVGEOp(w) => BVLEOp(w)
      case BVLEOp(w) => BVGEOp(w)
      case other => throw new NotImplementedError(s"missing swap for $other")
    }

    (a1, a2) match {
      case (e, lit @ BitVectorLit(_, _)) => simplifyCompareToConstant(op, e, lit)
      case (lit @ BitVectorLit(_, _), e) => simplifyCompareToConstant(swapOp, e, lit)
      case _ => super.simplifyBVCmp(op, a1, a2)
    }
  }

  private def simplifyCompareToConstant(op: BoolResultOp, e: Expr, lit: BitVectorLit): Expr = {
    def uniformMsbs(inner: Expr, by: Int): Boolean = {
      val inner_w = bitWidth(inner)
      assert(inner_w > 0)
      val mask = (BigInt(1) << (by + 1)) - 1
      val high_bits = (lit.value >> (inner_w - 1)) & mask
      // check for proper sign extension behavior of constant
      high_bits == 0 || high_bits == mask
    }
    def reducedOp(w: Int) = op match {
      case EqualityOp => EqualityOp
      case BVGTUOp(_) => BVGTUOp(w)
      case BVLTUOp(_) => BVLTUOp(w)
      case BVGEUOp(_) => BVGEUOp(w)
      case BVLEUOp(_) => BVLEUOp(w)
      case BVGTOp(_) => BVGTOp(w)
      case BVLTOp(_) => BVLTOp(w)
      case BVGEOp(_) => BVGEOp(w)
      case BVLEOp(_) => BVLEOp(w)
    }

    e match {
      case OperatorApplication(BVSignExtOp(w, by), List(inner)) if uniformMsbs(inner, by) =>
        OperatorApplication(reducedOp(w - by), List(inner, extractLiteral(lit.value, hi=(w - by - 1), lo=0)))
      case  other => OperatorApplication(op, List(other, lit))
    }
  }

  override protected def simplifyITE(cond: Expr, a: Expr, b: Expr): Expr = (cond, a, b) match {
    // toBV(toBool(e)) pattern ITE(e == 1bv1, 1bv1, 0bv1) <=> e
    case(OperatorApplication(EqualityOp, List(e, BV1)), BV1, BV0) => e
    case _ => super.simplifyITE(cond, a, b)
  }

  override protected def simplifyBVOp(op: BVResultOp, args: List[Expr]): Expr = (op, args) match {
    case (BVExtractOp(hi, lo), List(e)) => simplifyBVExtract(hi, lo, e)
    case (BVConcatOp(w), List(a, b)) => simplifyBVCat(w, a, b)
    case _ => super.simplifyBVOp(op, args)
  }

  private def simplifyBVCat(w: Int, a: Expr, b: Expr): Expr = (a, b) match {

    case (OperatorApplication(BVExtractOp(hi, lo), List(e1)), e2)
      if e1 == e2 && hi == lo && hi == bitWidth(e1) - 1
    => OperatorApplication(BVSignExtOp(w, 1), List(e2))

    case (OperatorApplication(BVExtractOp(hi, lo), List(e1)), OperatorApplication(BVSignExtOp(_, by), List(e2)))
      if e1 == e2 && hi == lo && hi == bitWidth(e1) - 1
    => OperatorApplication(BVSignExtOp(w, by + 1), List(e2))

    case _ => super.simplifyBVOp(BVConcatOp(w), List(a, b))
  }

  private def simplifyBVExtract(hi: Int, lo: Int, e: Expr): Expr = {
    // extract no-op
    if(lo == 0 && hi + 1 == bitWidth(e)) {
      e
    } else e match {
      case BitVectorLit(value, _) => extractLiteral(value, hi, lo)
      case OperatorApplication(BVConcatOp(_), List(msb, lsb)) => pushDownExtract(hi, lo, msb, lsb)
      case OperatorApplication(BVExtractOp(_, in_lo), args) => combineExtract(hi, lo, in_lo, args)
      case _=> super.simplifyBVOp(BVExtractOp(hi, lo), List(e))
    }
  }

  /** push extract through cat expressions */
  protected def pushDownExtract(hi: Int, lo: Int, msb: Expr, lsb: Expr): Expr = {
    val lsb_width = bitWidth(lsb)

    if(lsb_width > hi) {
      simplifyBVExtract(hi, lo, lsb)
    } else if(lo >= lsb_width) {
      simplifyBVExtract(hi - lsb_width, lo - lsb_width, msb)
    } else {
      val msb_ext = simplifyBVExtract(hi - lsb_width, 0, msb)
      val lsb_ext = simplifyBVExtract(lsb_width - 1, lo, lsb)
      app(BVConcatOp(hi - lo + 1), List(msb_ext, lsb_ext))
    }
  }
  protected def extractLiteral(value: BigInt, hi: Int, lo: Int): BitVectorLit = {
    assert(value >= 0, s"Cannot deal with negative BV values, what do they even mean? $value")
    val width = hi - lo + 1
    val mask = (BigInt(1) << width) - 1
    BitVectorLit((value >> lo) & mask, width)
  }

  protected def combineExtract(hi: Int, lo: Int, inner_lo: Int, args: List[Expr]): Expr = {
    val combined_lo = lo + inner_lo
    val combined_hi = hi + inner_lo
    app(BVExtractOp(combined_hi, combined_lo), args)
  }
}