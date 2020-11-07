// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.mc

import scala.collection.mutable
import maltese.smt

/** Encodes a TransitionSystem in the format of the Uclid5 model checking system.
 *  https://github.com/uclid-org/uclid
 * */
object Uclid5Serializer {
  def serialize(sys: TransitionSystem): Iterable[String] = {
    new Uclid5Serializer().serialize(sys)
  }
}


class Uclid5Serializer private() {
  def serialize(sys: TransitionSystem): Iterable[String] = {
    val module = s"module ${escape(sys.name)} {"
    val inputs = sys.inputs.map(i => s"  input ${escape(i.name)} : ${bvWidthToType(i.width)}")
    val outputs = sys.outputs.map(i => s"  input ${escape(i.name)} : ${bvWidthToType(i.width)}")

  }

  private def

  private def bvWidthToType(width: Int): String = if(width == 1) { "boolean" } else { s"bv$width" }
  private def escape(sym: smt.SMTSymbol): String = escape(sym.name)
  private def escape(name: String): String = name // TODO
}

private object Uclid5ExprSerializer {
  def serialize(e: smt.SMTExpr): String = e match {
    case b: smt.BVExpr => serialize(b)
    case a: smt.ArrayExpr => serialize(a)
  }

  def serialize(t: smt.SMTType): String = t match {
    case smt.BVType(width) => serializeBitVectorType(width)
    case smt.ArrayType(indexWidth, dataWidth) => serializeArrayType(indexWidth, dataWidth)
  }

  private def serialize(e: smt.BVExpr): String = e match {
    case smt.BVLiteral(value, width) =>
      val mask = (BigInt(1) << width) - 1
      val twosComplement = if (value < 0) { ((~(-value)) & mask) + 1 } else value
      if (width == 1) {
        if (twosComplement == 1) "true" else "false"
      } else {
        s"${twosComplement}bv$width"
      }
    case smt.BVSymbol(name, _)                            => escapeIdentifier(name)
    case smt.BVExtend(e, 0, _)                            => serialize(e)
    case smt.BVExtend(smt.BVLiteral(value, width), by, false) => serialize(smt.BVLiteral(value, width + by))
    case smt.BVExtend(e, by, signed) =>
      val foo = if (signed) "sign_extend" else "zero_extend"
      s"((_ $foo $by) ${asBitVector(e)})"
    case smt.BVSlice(e, hi, lo) =>
      if (lo == 0 && hi == e.width - 1) { serialize(e) }
      else {
        val bits = s"((_ extract $hi $lo) ${asBitVector(e)})"
        // 1-bit extracts need to be turned into a boolean
        if (lo == hi) { toBool(bits) }
        else { bits }
      }
    case smt.BVNot(smt.BVEqual(a, b)) if a.width == 1 => s"(distinct ${serialize(a)} ${serialize(b)})"
    case smt.BVNot(smt.BVNot(e))                      => serialize(e)
    case smt.BVNot(e) =>
      if (e.width == 1) { s"(not ${serialize(e)})" }
      else { s"(bvnot ${serialize(e)})" }
    case smt.BVNegate(e) => s"(bvneg ${asBitVector(e)})"
    case smt.BVImplies(smt.BVLiteral(v, 1), b) if v == 1     => serialize(b)
    case smt.BVImplies(a, b)                                 => s"(=> ${serialize(a)} ${serialize(b)})"
    case smt.BVEqual(a, b)                                   => s"(= ${serialize(a)} ${serialize(b)})"
    case smt.ArrayEqual(a, b)                                => s"(= ${serialize(a)} ${serialize(b)})"
    case smt.BVComparison(smt.Compare.Greater, a, b, false)      => s"(bvugt ${asBitVector(a)} ${asBitVector(b)})"
    case smt.BVComparison(smt.Compare.GreaterEqual, a, b, false) => s"(bvuge ${asBitVector(a)} ${asBitVector(b)})"
    case smt.BVComparison(smt.Compare.Greater, a, b, true)       => s"(bvsgt ${asBitVector(a)} ${asBitVector(b)})"
    case smt.BVComparison(smt.Compare.GreaterEqual, a, b, true)  => s"(bvsge ${asBitVector(a)} ${asBitVector(b)})"
    // boolean operations get a special treatment for 1-bit vectors aka bools
    case smt.BVOp(smt.Op.And, a, b) if a.width == 1 => s"(and ${serialize(a)} ${serialize(b)})"
    case smt.BVOp(smt.Op.Or, a, b) if a.width == 1  => s"(or ${serialize(a)} ${serialize(b)})"
    case smt.BVOp(smt.Op.Xor, a, b) if a.width == 1 => s"(xor ${serialize(a)} ${serialize(b)})"
    case smt.BVOp(op, a, b) if a.width == 1     => toBool(s"(${serialize(op)} ${asBitVector(a)} ${asBitVector(b)})")
    case smt.BVOp(op, a, b)                     => s"(${serialize(op)} ${serialize(a)} ${serialize(b)})"
    case smt.BVConcat(a, b)                     => s"(concat ${asBitVector(a)} ${asBitVector(b)})"
    case smt.ArrayRead(array, index)            => s"(select ${serialize(array)} ${asBitVector(index)})"
    case smt.BVIte(cond, tru, fals)             => s"(ite ${serialize(cond)} ${serialize(tru)} ${serialize(fals)})"
    case smt.BVFunctionCall(name, args, _)      => args.map(serializeArg).mkString(s"($name ", " ", ")")
    case smt.BVForall(variable, e) => s"(forall ((${variable.name} ${serialize(variable.tpe)})) ${serialize(e)})"
  }

  private def serialize(e: smt.ArrayExpr): String = e match {
    case smt.ArraySymbol(name, _, _)        => escapeIdentifier(name)
    case smt.ArrayStore(array, index, data) => s"(store ${serialize(array)} ${serialize(index)} ${serialize(data)})"
    case smt.ArrayIte(cond, tru, fals)      => s"(ite ${serialize(cond)} ${serialize(tru)} ${serialize(fals)})"
    case c @ smt.ArrayConstant(e, _)        => s"((as const ${serializeArrayType(c.indexWidth, c.dataWidth)}) ${serialize(e)})"
    case smt.ArrayFunctionCall(name, args, _, _) => args.map(serializeArg).mkString(s"($name ", " ", ")")
  }

  private def serializeArrayType(indexWidth: Int, dataWidth: Int): String =
    s"(Array ${serializeBitVectorType(indexWidth)} ${serializeBitVectorType(dataWidth)})"
  private def serializeBitVectorType(width: Int): String =
    if (width == 1) { "Bool" } else { assert(width > 1); s"(_ BitVec $width)" }


  private def serialize(op: smt.Op.Value): String = op match {
    case smt.Op.And                  => "&&"
    case smt.Op.Or                   => "||"
    case smt.Op.Xor                  => "^"
    case smt.Op.ArithmeticShiftRight => throw new NotImplementedError("ashr")
    case smt.Op.ShiftRight           => throw new NotImplementedError("lshr")
    case smt.Op.ShiftLeft            => throw new NotImplementedError("lshl")
    case smt.Op.Add                  => "+"
    case smt.Op.Mul                  => "*"
    case smt.Op.Sub                  => "-"
    case smt.Op.SignedDiv            => throw new NotImplementedError("sdiv")
    case smt.Op.UnsignedDiv          => throw new NotImplementedError("udiv")
    case smt.Op.SignedMod            => throw new NotImplementedError("smod")
    case smt.Op.SignedRem            => "%"
    case smt.Op.UnsignedRem          => "%_u"
  }

  private def toBool(e: String): String = s"$e == 1bv1"

  private val bvZero = "0bv1"
  private val bvOne = "1bv1"
  private def asBitVector(e: smt.BVExpr): String =
    if (e.width > 1) { serialize(e) }
    else { s"if (${serialize(e)}) then ($bvOne) else ($bvZero)" }

  private def escapeIdentifier(name: String): String = name // TODO
}