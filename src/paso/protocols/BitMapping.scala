// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import maltese.smt

/** helper functions for mappings individual bits of bitvector expressions while trying to retain the word structure */
object BitMapping {
  def analyze(alreadyMapped: BigInt, lhs: smt.BVExpr, s: smt.BVSymbol, hi: Int, lo: Int): (smt.BVExpr, smt.BVExpr, BigInt) = {
    val width = hi - lo + 1
    val mask = ((BigInt(1) << width) - 1) << lo
    val newBits = (~alreadyMapped) & mask
    val oldBits = alreadyMapped & mask
    val rhs = if(width == s.width) { s } else { smt.BVSlice(s, hi, lo) }
    // oldBits only make constraints, newBits create a new mapping
    (mapBits(lhs, rhs, oldBits >> lo), mapBits(lhs, rhs, newBits >> lo), alreadyMapped | mask)
  }

  def mapBits(lhs: smt.BVExpr, rhs: smt.BVExpr, mask: BigInt): smt.BVExpr = {
    assert(lhs.width == rhs.width)
    if(mask == 0) { return smt.True() }
    val intervals = findIntervals(mask, lhs.width)
    val eqs = intervals.map { case (hi, lo) =>
      smt.BVEqual(smt.BVSlice(lhs, hi, lo), smt.BVSlice(rhs, hi, lo))
    }
    simplify(smt.BVAnd(eqs))
  }

  /** e.g. findIntervals(011001, 6) = List((0,0), (4,3)) */
  def findIntervals(mask: BigInt, width: Int): List[(Int, Int)] = {
    if(mask == 0) { return List() }
    var msb = findOne(mask, width - 1).get
    var intervals: List[(Int, Int)] = List()
    while(msb >= 0) {
      val lsb = findZero(mask, msb).map(_ + 1).getOrElse(0)
      intervals = intervals :+ (msb, lsb)
      msb = if(lsb == 0) { -1 } else { findOne(mask, lsb - 1).getOrElse(-1) }
    }
    intervals
  }

  private def findOne(mask: BigInt, msb: Int): Option[Int] = (msb to 0 by -1).find(isSet(mask, _))
  private def findZero(mask: BigInt, msb: Int): Option[Int] = (msb to 0 by -1).find(!isSet(mask, _))
  private def isSet(value: BigInt, bit: Int): Boolean = (value & (BigInt(1) << bit)) != 0

  def simplify(e: smt.BVExpr): smt.BVExpr = smt.SMTSimplifier.simplify(e).asInstanceOf[smt.BVExpr]
}
