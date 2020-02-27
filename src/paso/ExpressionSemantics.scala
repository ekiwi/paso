// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>


package paso

import firrtl.ir._
import firrtl.PrimOps._
import uclid.smt

trait ExpressionSemantics {
  val argCount : Int
  val paramCount : Int
  def resultType(ts: Seq[Type], params: Seq[BigInt] = Seq()) : Option[Type]
}

object BitUtils {
  def makeMaskBig(w: Int): BigInt = ???
}

trait TypeHelpers {
  protected def getWidth(tpe: Type) : Int = tpe match {
    case UIntType(IntWidth(w)) => w.toInt
    case SIntType(IntWidth(w)) => w.toInt
    case other => throw new RuntimeException(s"Cannot get width for type: $other")
  }

  protected def isSigned(tpe: Type): Boolean = tpe match {
    case SIntType(_) => true
    case _ => false
  }

  // TODO: remove this back, potentially after we implement a read UInt<1> -> Bool analysis pass
  protected def toBool(e: smt.Expr): smt.Expr = if(e.typ.isBool) { e } else {
    smt.OperatorApplication(smt.EqualityOp, List(e, smt.BitVectorLit(1,1 )))
  }
  protected def toBV(e: smt.Expr): smt.Expr = if(e.typ.isBitVector) { e } else {
    smt.OperatorApplication(smt.ITEOp, List(e, smt.BitVectorLit(1, 1), smt.BitVectorLit(0, 1)))
  }

  protected def extend(inBits: Int, outBits: Int, signed: Boolean) : smt.Expr => smt.Expr = {
    assert(inBits <= outBits,  "This method only extends the width of an argument!")
    if(inBits == outBits) { e => e }
    else{
      val op = if(signed){ smt.BVSignExtOp(outBits, outBits - inBits) }
      else { smt.BVZeroExtOp(outBits, outBits - inBits) }
      if(inBits == 1) e => smt.OperatorApplication(op, List(toBV(e)))
      else e => smt.OperatorApplication(op, List(e))
    }
  }

  protected def extractAsBool(bitPos: Int) : smt.Expr => smt.Expr = e => {
    val bit = smt.OperatorApplication(smt.BVExtractOp(bitPos, bitPos), List(e))
    smt.OperatorApplication(smt.EqualityOp, List(bit, smt.BitVectorLit(1, 1)))
  }
}

object BinOpCompiler {
  type ConFun = (BigInt, BigInt) => BigInt
  type SymFun = (smt.Expr, smt.Expr) => smt.Expr
  def compile(op: PrimOp, t1: Type, t2: Type, tr: Type): (ConFun, SymFun) =
    opToSemantics(op).compileAndCheck(t1, t2, tr)
  def opToSemantics(op: PrimOp): BinOpSemantics = op match {
    case Add => AddSemantics
    case Sub => SubSemantics
    case Mul => MulSemantics
    case Div => DivSemantics
    case Rem => RemSemantics
    case Eq  => EqSemantics
    case Neq => NeqSemantics
    case Lt  => LtSemantics
    case Leq => LeqSemantics
    case Gt  => GtSemantics
    case Geq => GeqSemantics
    case Dshl => DshlSemantics
    case Dshr => DshrSemantics
    case And => AndSemantics
    case Or  => OrSemantics
    case Xor => XorSemantics
    case Cat => CatSemantics
    case other => throw new RuntimeException(s"Op $other is not a BinOp!")
  }
}

trait BinOpSemantics extends ExpressionSemantics with TypeHelpers {
  override val argCount = 2
  override val paramCount = 0


  override def resultType(ts: Seq[Type], params: Seq[BigInt] = Seq()) : Option[Type] = {
    assert(ts.size == 2)
    assert(params.isEmpty)
    resultType(ts.head, ts(1))
  }

  def resultType(t1: Type, t2: Type) : Option[Type] = (t1, t2) match {
    case (UIntType(IntWidth(w1)), UIntType(IntWidth(w2))) =>
      Some(UIntType(IntWidth(uIntResultWidth(w1, w2))))
    case (SIntType(IntWidth(w1)), SIntType(IntWidth(w2))) =>
      Some(SIntType(IntWidth(sIntResultWidth(w1, w2))))
    case _ => None
  }

  type ConFun = BinOpCompiler.ConFun
  type SymFun = BinOpCompiler.SymFun

  protected def compileCon(w1: Int, w2: Int, wr: Int) : ConFun

  def typeCheck(t1: Type, t2: Type, tr: Type) : Boolean = resultType(t1,t2).contains(tr)

  def compile(t1: Type, t2: Type, tr: Type) : (ConFun, SymFun) = {
    val (w1, w2, wr) = (getWidth(t1), getWidth(t2), getWidth(tr))
    (compileCon(w1, w2, wr), compileSym(w1, w2, wr, isSigned(tr)))
  }

  def compileAndCheck(t1: Type, t2: Type, tr: Type) : (ConFun, SymFun) = {
    assert(typeCheck(t1, t2, tr), s"Expressions does not type-check, expected ${resultType(t1, t2)} not $tr!")
    assert(getWidth(t1) > 0 && getWidth(t2) > 0, s"No support for 0-width types! ($t1, $t2, $tr)")
    compile(t1, t2, tr)
  }

  protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun

  protected def uIntResultWidth(w1: BigInt, w2: BigInt) : BigInt
  protected def sIntResultWidth(w1: BigInt, w2: BigInt) : BigInt
}

trait ArithmeticSemantics extends BinOpSemantics {
  protected def op(w: Int) : smt.Operator
  protected def boolOp : smt.BoolResultOp
  override protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun = {
    if(wr == 1 && !signed) {
      assert(w1 == 1)
      assert(w2 == 1)
      (a, b) => smt.OperatorApplication(boolOp, List(toBool(a), toBool(b)))
    } else {
      (a, b) => {
        smt.OperatorApplication(op(wr), List(extend(w1, wr, signed)(a), extend(w2, wr, signed)(b)))
      }
    }
  }
}

object AddSemantics extends ArithmeticSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2) + 1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2) + 1
  override protected def op(w: Int) = smt.BVAddOp(w)
  override protected def boolOp = smt.InequalityOp
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => e1 + e2
}

object SubSemantics extends ArithmeticSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2) + 1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2) + 1
  override protected def op(w: Int) = smt.BVSubOp(w)
  override protected def boolOp = throw new NotImplementedError("Sub as bool...")
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => e1 - e2
}

object MulSemantics extends ArithmeticSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1 + w2
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1 + w2
  override protected def op(w: Int) = smt.BVMulOp(w)
  override protected def boolOp = smt.ConjunctionOp
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => e1 * e2
}

trait RemDivSemantics extends BinOpSemantics {
  protected def op(w: Int) : smt.Operator
  override protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun = (a,b) => {
    val e2 = extend(w2, wr, signed)(b)
    val zero = smt.BitVectorLit(0, wr)
    val is_zero = smt.OperatorApplication(smt.EqualityOp, List(e2, zero))
    val res = smt.OperatorApplication(op(wr), List(extend(w1, wr, signed)(a), e2))
    smt.OperatorApplication(smt.ITEOp, List(is_zero, zero, res))
  }
}

object DivSemantics extends RemDivSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1 + 1
  override protected def op(w: Int) =
    throw new NotImplementedError("BVDivOp is only available in an unpublished version of Uclid")//smt.BVDivOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e2 == 0) { 0 } else { e1 / e2}
}

object RemSemantics extends RemDivSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1.min(2)
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1.min(2)
  override protected def op(w: Int) =
    throw new NotImplementedError("BVRemOp is only available in an unpublished version of Uclid")//smt.BVRemOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e2 == 0) { 0 } else { e1 % e2}
}

trait ComparisonSemantics extends BinOpSemantics {
  protected def op(w: Int, signed: Boolean) : smt.Operator
  // small fix as comparisons always return an unsigned result
  override def resultType(t1: Type, t2: Type) : Option[Type] =
    super.resultType(t1, t2).map( _ => UIntType(IntWidth(1)))
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = 1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = 1
  override protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun = {
    val we = math.max(w1, w2)
    if(we == 1) {
      assert(w1 == 1 && w2 == 1)
      (a, b) => {
        smt.OperatorApplication(op(we, signed), List(toBool(a), toBool(b)))
      }
    } else {
      (a, b) => {
        smt.OperatorApplication(op(we, signed), List(extend(w1, we, signed)(a), extend(w2, we, signed)(b)))
      }
    }
  }
}

object EqSemantics extends ComparisonSemantics {
  override protected def op(w: Int, signed: Boolean) = smt.EqualityOp
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 == e2) { 1 } else { 0 }
}

object NeqSemantics extends ComparisonSemantics {
  override protected def op(w: Int, signed: Boolean) = smt.InequalityOp
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 != e2) { 1 } else { 0 }
}

object LtSemantics extends ComparisonSemantics {
  override protected def op(w: Int, signed: Boolean) = if(signed) { smt.BVLTOp(w) } else { smt.BVLTUOp(w) }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 < e2) { 1 } else { 0 }
}

object LeqSemantics extends ComparisonSemantics {
  override protected def op(w: Int, signed: Boolean) = if(signed) { smt.BVLEOp(w) } else { smt.BVLEUOp(w) }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 <= e2) { 1 } else { 0 }
}

object GtSemantics extends ComparisonSemantics {
  override protected def op(w: Int, signed: Boolean) = if(signed) { smt.BVGTOp(w) } else { smt.BVGTUOp(w) }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 > e2) { 1 } else { 0 }
}

object GeqSemantics extends ComparisonSemantics {
  override protected def op(w: Int, signed: Boolean) = if(signed) { smt.BVGEOp(w) } else { smt.BVGEUOp(w) }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 >= e2) { 1 } else { 0 }
}

trait BitwiseSemantics extends ArithmeticSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2)
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2)
}

object AndSemantics extends BitwiseSemantics {
  override protected def op(w: Int) = smt.BVAndOp(w)
  override protected def boolOp = smt.ConjunctionOp
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = {
    val mask = BitUtils.makeMaskBig(wr)
    (e1, e2) => (e1 & e2) & mask
  }
}

object OrSemantics extends BitwiseSemantics {
  override protected def op(w: Int) = smt.BVOrOp(w)
  override protected def boolOp = smt.DisjunctionOp
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = {
    val mask = BitUtils.makeMaskBig(wr)
    (e1, e2) => (e1 | e2) & mask
  }
}

object XorSemantics extends BitwiseSemantics {
  override protected def op(w: Int) = smt.BVXorOp(w)
  override protected def boolOp = smt.InequalityOp
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = {
    val mask = BitUtils.makeMaskBig(wr)
    (e1, e2) => (e1 ^ e2) & mask
  }
}

trait DynamicShiftSemantics extends BinOpSemantics {
  override def resultType(t1: Type, t2: Type) : Option[Type] = (t1, t2) match {
    case (UIntType(IntWidth(w1)), UIntType(IntWidth(w2))) =>
      Some(UIntType(IntWidth(uIntResultWidth(w1, w2))))
    case (SIntType(IntWidth(w1)), UIntType(IntWidth(w2))) =>
      Some(SIntType(IntWidth(sIntResultWidth(w1, w2))))
    case _ => None
  }
  protected def op(w: Int, signed: Boolean) : smt.Operator
  override protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun = (a,b) => {
    smt.OperatorApplication(op(wr, signed), List(extend(w1, wr, signed)(a), extend(w2, wr, signed)(b)))
  }
}

object DshlSemantics extends DynamicShiftSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1 + BigInt(2).pow(w2.toInt) - 1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1 + BigInt(2).pow(w2.toInt) - 1
  override protected def op(w: Int, signed: Boolean) = smt.BVLeftShiftBVOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => e1 << e2.toInt
}

object DshrSemantics extends DynamicShiftSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1
  override protected def op(w: Int, signed: Boolean) =
    if(signed) { smt.BVARightShiftBVOp(w) } else { smt.BVLRightShiftBVOp(w) }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => e1 >> e2.toInt
}

object CatSemantics extends BinOpSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1 + w2
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1 + w2
  override protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun = (a,b) => {
    smt.OperatorApplication(smt.BVConcatOp(wr), List(toBV(a), toBV(b)))
  }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = {
    val mask1 = BitUtils.makeMaskBig(w1)
    (e1, e2) => ((e1 & mask1) << w2) | e2
  }
}

object UnOpCompiler {
  type ConFun = BigInt => BigInt
  type SymFun = smt.Expr => smt.Expr
  def compile(op: PrimOp, t1: Type, tr: Type, params: Seq[BigInt] = Seq()): (ConFun, SymFun) =
    opToSemantics(op).compileAndCheck(t1, tr, params)
  def opToSemantics(op: PrimOp): UnOpSemantics = op match {
    case AsUInt       => AsUIntSemantics
    case AsSInt       => AsSIntSemantics
    case AsClock      => AsClockSemantics
    case AsAsyncReset => AsAsyncResetSemantics
    case Cvt          => CvtSemantics
    case Neg          => NegSemantics
    case Not          => NotSemantics
    case Andr         => AndRSemantics
    case Orr          => OrRSemantics
    case Xorr         => XorRSemantics
    case Shl  => ShlSemantics
    case Shr  => ShrSemantics
    case Pad  => PadSemantics
    case Head => HeadSemantics
    case Tail => TailSemantics
    case Bits => BitsSemantics
    case other => throw new RuntimeException(s"Op $other is not an UnOp!")
  }
}

trait UnOpSemantics extends ExpressionSemantics with TypeHelpers {
  override val argCount = 1
  type ConFun = UnOpCompiler.ConFun
  type SymFun = UnOpCompiler.SymFun

  override def resultType(ts: Seq[Type], params: Seq[BigInt] = Seq()) : Option[Type] = {
    assert(ts.size == 1)
    assert(params.size == paramCount)
    resultType(ts.head, params)
  }

  protected def resultType(t1: Type, params: Seq[BigInt]): Option[Type]

  def typeCheck(t1: Type, tr: Type, params: Seq[BigInt]) : Boolean = resultType(t1, params).contains(tr)

  def compileAndCheck(t1: Type, tr: Type, params: Seq[BigInt]) : (ConFun, SymFun) = {
    assert(params.size == paramCount, s"${params.size} != $argCount")
    assert(typeCheck(t1, tr, params), "Expressions does not type-check!")
    assert(getWidth(t1) > 0, s"No support for 0-width types! ($t1, $tr)")
    compile(t1, tr, params)
  }

  def compile(t1: Type, tr: Type, params: Seq[BigInt]) : (ConFun, SymFun)
}

trait UnOpZeroArgSemantics extends UnOpSemantics {
  override val paramCount = 0
  def compile(t1: Type, tr: Type, params: Seq[BigInt]) : (ConFun, SymFun) = {
    val (w1, wr, signed) = (getWidth(t1), getWidth(tr),isSigned(tr))
    (compileCon(w1, wr, signed), compileSym(w1, wr, signed))
  }
  def compileCon(w1: Int, wr: Int, signed: Boolean) : ConFun
  protected def compileSym(w1: Int, wr: Int, signed: Boolean) : SymFun
  protected def resultType(t1: Type, params: Seq[BigInt]): Option[Type] = resultType(t1)
  def resultType(t1: Type): Option[Type]
}

object AsUIntSemantics extends UnOpZeroArgSemantics {
  override def resultType(t1: Type) : Option[Type] = t1 match {
    case UIntType(IntWidth(w)) => Some(UIntType(IntWidth(w)))
    case SIntType(IntWidth(w)) => Some(UIntType(IntWidth(w)))
    case ClockType => Some(UIntType(IntWidth(1)))
    case _ => None
  }
  override def compileCon(w1: Int, wr: Int, signed: Boolean) : ConFun = {
    val mask = BitUtils.makeMaskBig(wr)
    if(signed) { e1 => e1 & mask } else { e1 => e1 }
  }
  override protected def compileSym(w1: Int, wr: Int, signed: Boolean) : SymFun = e1 => e1
}

object AsSIntSemantics extends UnOpZeroArgSemantics {
  override def resultType(t1: Type) : Option[Type] = t1 match {
    case UIntType(IntWidth(w)) => Some(SIntType(IntWidth(w)))
    case SIntType(IntWidth(w)) => Some(SIntType(IntWidth(w)))
    case ClockType => Some(SIntType(IntWidth(1)))
    case _ => None
  }
  override def compileCon(w1: Int, wr: Int, signed: Boolean) : ConFun = ???
  override protected def compileSym(w1: Int, wr: Int, signed: Boolean) : SymFun = e1 => e1
}

object AsClockSemantics extends UnOpZeroArgSemantics {
  override def resultType(t1: Type) : Option[Type] = t1 match {
    case UIntType(IntWidth(w)) => if(w == 1) { Some(ClockType) } else { None }
    case SIntType(IntWidth(w)) => if(w == 1) { Some(ClockType) } else { None }
    case ClockType => Some(ClockType)
    case _ => None
  }
  override def compileCon(w1: Int, wr: Int, signed: Boolean) : ConFun = e1 => e1
  override protected def compileSym(w1: Int, wr: Int, signed: Boolean) : SymFun = e1 => e1
}

object AsAsyncResetSemantics extends UnOpZeroArgSemantics {
  override def resultType(t1: Type) : Option[Type] =  {
    throw new NotImplementedError("TODO: implement AsAsyncResetSemantics")
  }
  override def compileCon(w1: Int, wr: Int, signed: Boolean) : ConFun = {
    throw new NotImplementedError("TODO: implement AsAsyncResetSemantics")
  }
  override protected def compileSym(w1: Int, wr: Int, signed: Boolean) : SymFun = {
    throw new NotImplementedError("TODO: implement AsAsyncResetSemantics")
  }
}

object CvtSemantics extends UnOpZeroArgSemantics {
  override def resultType(t1: Type) : Option[Type] = t1 match {
    case UIntType(IntWidth(w)) => Some(SIntType(IntWidth(w + 1)))
    case SIntType(IntWidth(w)) => Some(SIntType(IntWidth(w)))
    case _ => None
  }
  override def compileCon(w1: Int, wr: Int, signed: Boolean) : ConFun = e1 => e1
  override protected def compileSym(w1: Int, wr: Int, signed: Boolean) : SymFun =
    if(signed) { e1 => e1 } else { e1 => smt.OperatorApplication(smt.BVZeroExtOp(wr, 1), List(e1)) }
}

object NegSemantics extends UnOpZeroArgSemantics {
  override def resultType(t1: Type) : Option[Type] = t1 match {
    case UIntType(IntWidth(w)) => Some(SIntType(IntWidth(w + 1)))
    case SIntType(IntWidth(w)) => Some(SIntType(IntWidth(w + 1)))
    case _ => None
  }
  override def compileCon(w1: Int, wr: Int, signed: Boolean) : ConFun = e1 => -e1
  override protected def compileSym(w1: Int, wr: Int, signed: Boolean) : SymFun = e1 =>
      smt.OperatorApplication(smt.BVSubOp(wr), List(smt.BitVectorLit(0, wr), extend(w1, wr, signed)(e1)))
}

object NotSemantics extends UnOpZeroArgSemantics {
  override def resultType(t1: Type) : Option[Type] = t1 match {
    case UIntType(IntWidth(w)) => Some(UIntType(IntWidth(w)))
    case SIntType(IntWidth(w)) => Some(UIntType(IntWidth(w)))
    case _ => None
  }
  override def compileCon(w1: Int, wr: Int, signed: Boolean) : ConFun = {
    val mask = BitUtils.makeMaskBig(w1)
    e1 => (~e1) & mask
  }
  override protected def compileSym(w1: Int, wr: Int, signed: Boolean) : SymFun = if(wr == 1) {
    e1 => smt.OperatorApplication(smt.NegationOp, List(e1))
  } else {
    e1 => smt.OperatorApplication(smt.BVNotOp(wr), List(e1))
  }
}

trait BitwiseReductionSemantics extends UnOpZeroArgSemantics {
  override def resultType(t1: Type) : Option[Type] = t1 match {
    case UIntType(IntWidth(w)) => Some(UIntType(IntWidth(1)))
    case SIntType(IntWidth(w)) => Some(UIntType(IntWidth(1)))
    case _ => None
  }
  protected val op : smt.BoolResultOp
  override protected def compileSym(w1: Int, wr: Int, signed: Boolean) : SymFun = e1 => {
    val bits = 0 until w1 map(b => extractAsBool(b)(e1))
    bits.reduce((a,b) => smt.OperatorApplication(op, List(a, b)))
  }
}

object AndRSemantics extends BitwiseReductionSemantics {
  override protected val op = smt.ConjunctionOp
  override def compileCon(w1: Int, wr: Int, signed: Boolean) : ConFun = {
    val mask = BitUtils.makeMaskBig(w1)
    e1 => if((e1 & mask) == mask) { 1 } else { 0 }
  }
}

object OrRSemantics extends BitwiseReductionSemantics {
  override protected val op = smt.DisjunctionOp
  override def compileCon(w1: Int, wr: Int, signed: Boolean) : ConFun = {
    val mask = BitUtils.makeMaskBig(w1)
    e1 => if((e1 & mask) > 0) { 1 } else { 0 }
  }
}

object XorRSemantics extends BitwiseReductionSemantics {
  override protected val op = smt.InequalityOp
  override def compileCon(w1: Int, wr: Int, signed: Boolean) : ConFun = {
    val mask = BitUtils.makeMaskBig(w1)
    e1 => {
      val uInt = e1 & mask
      (0 until w1).map(n => ((uInt >> n) & BigInt(1)).toInt).reduce(_ ^ _)
    }
  }
}

trait UnOpWithArgSemantics extends UnOpSemantics {
  override val paramCount = 1
  def compile(t1: Type, tr: Type, params: Seq[BigInt]) : (ConFun, SymFun) = {
    val (w1, wr, signed) = (getWidth(t1), getWidth(tr),isSigned(tr))
    (compileCon(w1, wr, signed, params.head), compileSym(w1, wr, signed, params.head))
  }
  def compileCon(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : ConFun
  def compileSym(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : SymFun
  protected def resultType(t1: Type, params: Seq[BigInt]): Option[Type] = resultType(t1, params.head)
  def resultType(t1: Type, param0: BigInt) : Option[Type]
}

object ShlSemantics extends UnOpWithArgSemantics {
  override def resultType(t1: Type, param0: BigInt) : Option[Type] =
    if(param0 < 0) { None } else {
      t1 match {
        case UIntType(IntWidth(w)) => Some(UIntType(IntWidth(w + param0)))
        case SIntType(IntWidth(w)) => Some(SIntType(IntWidth(w + param0)))
        case _ => None
      }
    }
  override def compileCon(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : ConFun = e1 => e1 << param0.toInt
  override def compileSym(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : SymFun = {
    if(param0 == 0) { e1 => e1 } else { e1 =>
      smt.OperatorApplication(smt.BVConcatOp(wr), List(e1, smt.BitVectorLit(0, param0.toInt)))
    }
  }
}

object ShrSemantics extends UnOpWithArgSemantics {
  private def resultWidth(w: BigInt, n: BigInt) = IntWidth((w - n).max(1))
  override def resultType(t1: Type, param0: BigInt) : Option[Type] =
    if(param0 < 0) { None } else {
      t1 match {
        case UIntType(IntWidth(w)) => Some(UIntType(resultWidth(w, param0)))
        case SIntType(IntWidth(w)) => Some(SIntType(resultWidth(w, param0)))
        case _ => None
      }
    }
  override def compileCon(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : ConFun = e1 => e1 >> param0.toInt
  override def compileSym(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : SymFun = {
    val msb = w1 - 1
    if(param0 == 0) { e1 => e1 }
    else if(param0 >= w1) {
      // if n is greater than or equal to the bit-width of e
      if(signed) { extractAsBool(msb) } else { e => smt.BooleanLit(false) }
    } else {
      val lsb = param0.toInt
      assert(msb - lsb + 1 == wr)
      e1 => smt.OperatorApplication(smt.BVExtractOp(msb, lsb), List(e1))
    }
  }
}

object PadSemantics extends UnOpWithArgSemantics {
  override def resultType(t1: Type, param0: BigInt) : Option[Type] =
    if(param0 < 0) { None } else {
      t1 match {
        case UIntType(IntWidth(w)) => Some(UIntType(IntWidth(w.max(param0))))
        case SIntType(IntWidth(w)) => Some(SIntType(IntWidth(w.max(param0))))
        case _ => None
      }
    }
  override def compileCon(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : ConFun = e1 => e1
  override def compileSym(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : SymFun = extend(w1, wr, signed)
}

object HeadSemantics extends UnOpWithArgSemantics {
  override def resultType(t1: Type, param0: BigInt) : Option[Type] =
    if(param0 <= 0 || param0 > getWidth(t1)) { None } else {
      t1 match {
        case UIntType(IntWidth(_)) => Some(UIntType(IntWidth(param0)))
        case SIntType(IntWidth(_)) => Some(UIntType(IntWidth(param0)))
        case _ => None
      }
    }
  override def compileCon(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : ConFun = {
    val mask = BitUtils.makeMaskBig(param0.toInt)
    val shift = w1 - param0.toInt
    e1 => (e1 >> shift) & mask
  }
  override def compileSym(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : SymFun =
    ShrSemantics.compileSym(w1, wr, signed, w1 - wr)
}

object TailSemantics extends UnOpWithArgSemantics {
  override def resultType(t1: Type, param0: BigInt) : Option[Type] =
    if(param0 < 0 || param0 >= getWidth(t1)) { None } else {
      t1 match {
        case UIntType(IntWidth(w)) => Some(UIntType(IntWidth(w - param0)))
        case SIntType(IntWidth(w)) => Some(UIntType(IntWidth(w - param0)))
        case _ => None
      }
    }
  override def compileCon(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : ConFun = {
    val mask = BitUtils.makeMaskBig(wr)
    e1 => e1 & mask
  }
  override def compileSym(w1: Int, wr: Int, signed: Boolean, param0: BigInt) : SymFun =
    BitsSemantics.compileSym(high = wr-1, low = 0)
}

object BitsSemantics extends UnOpSemantics {
  override val paramCount = 2

  override def resultType(t1: Type, params: Seq[BigInt]) : Option[Type] = {
    assert(params.size == 2)
    val (hi, lo) = (params.head, params(1))
    if(hi < lo) { None }
    else if(hi < 0 || hi >= getWidth(t1)) { None }
    else if(lo < 0 || lo >= getWidth(t1)) { None }
    else { t1 match {
      case UIntType(IntWidth(_)) => Some(UIntType(IntWidth(hi - lo + 1)))
      case SIntType(IntWidth(_)) => Some(UIntType(IntWidth(hi - lo + 1)))
      case _ => None
    } }
  }

  def compile(t1: Type, tr: Type, params: Seq[BigInt]) : (ConFun, SymFun) = {
    assert(params.size == 2)
    assert(t1 != tr)
    val (hi, lo) = (params.head, params(1))
    val (w1, wr) = (getWidth(t1), getWidth(tr))
    val mask = BitUtils.makeMaskBig(wr)
    val (high, low) = (hi.toInt, lo.toInt)
    val con : ConFun = e => (e >> low) & mask
    (con, compileSym(high, low))
  }

  def compileSym(high: Int, low: Int) : SymFun = {
    if(high > low) {
      e => smt.OperatorApplication(smt.BVExtractOp(high, low), List(e))
    } else {
      e => toBool(smt.OperatorApplication(smt.BVExtractOp(high, low), List(e)))
    }
  }
}

object MuxSemantics extends ExpressionSemantics with TypeHelpers {
  override val argCount = 3
  override val paramCount = 0

  type ConFun = (BigInt, BigInt, BigInt) => BigInt
  type SymFun = (smt.Expr, smt.Expr, smt.Expr) => smt.Expr

  override def resultType(ts: Seq[Type], params: Seq[BigInt]): Option[Type] = {
    assert(params.isEmpty)
    assert(ts.size == argCount)
    val (cond, a, b) = (ts.head, ts(1), ts(2))
    if(cond != UIntType(IntWidth(1))) { None }
    else if(a != b) { None }
    else { Some(a) }
  }

  def typeCheck(tcond: Type, ta: Type, tb: Type, tr: Type) : Boolean =
    resultType(Seq(tcond, ta, tb), Seq()).contains(tr)

  val con : ConFun = (cond, a, b) => if(cond != 0) a else b
  val sym : SymFun = (cond, a, b) => smt.OperatorApplication(smt.ITEOp, List(cond, a, b))
}