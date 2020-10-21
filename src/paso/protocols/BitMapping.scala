// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import maltese.smt

/** helper functions for mappings individual bits of bitvector expressions while trying to retain the word structure */
object BitMapping {
  def analyze(mappedBits: Map[String, BigInt], lhs: smt.BVExpr, rhs: smt.BVExpr):
  (List[smt.BVExpr], List[smt.BVExpr], Map[String, BigInt]) = rhs match {
    case smt.BVConcat(a, b) =>
      val aRes = analyze(mappedBits, smt.BVSlice(lhs, lhs.width - 1, b.width), a)
      val bRes = analyze(aRes._3, smt.BVSlice(lhs, b.width - 1, 0), b)
      (aRes._1 ++ bRes._1, aRes._2 ++ bRes._2, bRes._3)
    case smt.BVSlice(s: smt.BVSymbol, hi, lo) =>
      val res = analyze(mappedBits(s.name), lhs, s, hi, lo)
      (List(res._1), List(res._2), mappedBits + (s.name -> res._3))
    case s : smt.BVSymbol =>
      val res = analyze(mappedBits(s.name), lhs, s, s.width - 1, 0)
      (List(res._1), List(res._2), mappedBits + (s.name -> res._3))
    case l : smt.BVLiteral =>
      (List(smt.BVEqual(lhs, l)), List(), mappedBits)
  }

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
    smt.BVAnd(eqs)
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

  def mappedBits(e: smt.SMTExpr): Map[String, BigInt] = e match {
    case smt.BVSlice(smt.BVSymbol(name, _), hi, lo) => Map(name -> toMask(hi, lo))
    case smt.BVSymbol(name, width) => Map(name -> toMask(width))
    case other =>
      if(other.children.isEmpty) { Map() }
      else if(other.children.size == 1) { mappedBits(other.children.head) }
      else {
        val maps = other.children.flatMap(c => mappedBits(c).toSeq)
        maps.foldLeft(Map[String, BigInt]()){ case (map, (name, bits)) =>
          map + (name -> (bits | map.getOrElse(name, BigInt(0))))
        }
      }
  }

  private def toMask(width: Int): BigInt = (BigInt(1) << width) - 1
  def toMask(hi: Int, lo: Int): BigInt = toMask(hi-lo+1) << lo
  private def findOne(mask: BigInt, msb: Int): Option[Int] = (msb to 0 by -1).find(isSet(mask, _))
  private def findZero(mask: BigInt, msb: Int): Option[Int] = (msb to 0 by -1).find(!isSet(mask, _))
  private def isSet(value: BigInt, bit: Int): Boolean = (value & (BigInt(1) << bit)) != 0
}
