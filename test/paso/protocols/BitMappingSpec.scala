// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import maltese.smt

import org.scalatest.flatspec.AnyFlatSpec

class BitMappingSpec extends AnyFlatSpec {
  def simplify(e: smt.BVExpr): smt.BVExpr = smt.SMTSimplifier.simplify(e).asInstanceOf[smt.BVExpr]

  "findIntervals" should "find all the intervals" in {
    assert(BitMapping.findIntervals(BigInt("0011010", 2), 7) == List((4,3), (1,1)))
    assert(BitMapping.findIntervals(BigInt("1011010", 2), 7) == List((6,6), (4,3), (1,1)))
    assert(BitMapping.findIntervals(BigInt("1111010", 2), 7) == List((6,3), (1,1)))
    assert(BitMapping.findIntervals(BigInt("1111011", 2), 7) == List((6,3), (1,0)))
    assert(BitMapping.findIntervals(BigInt("1110101", 2), 7) == List((6,4), (2,2), (0,0)))
    assert(BitMapping.findIntervals(BigInt("1010101", 2), 7) == List((6,6), (4,4), (2,2), (0,0)))
    assert(BitMapping.findIntervals(BigInt("0101010", 2), 7) == List((5,5), (3,3), (1,1)))
    assert(BitMapping.findIntervals(BigInt("0011010", 2), 3) == List((1,1)))
  }

  "mapBits" should "correctly map bits" in {
    val (a,b) = (smt.BVSymbol("a", 7), smt.BVSymbol("b", 10))
    val bSlice = smt.BVSlice(b, 8, 2)

    assert(simplify(BitMapping.mapBits(a, bSlice, BigInt("0011010", 2))) ==
      smt.BVAnd(smt.BVEqual(smt.BVSlice(a, 4, 3), smt.BVSlice(b, 6, 5)),
                smt.BVEqual(smt.BVSlice(a, 1, 1), smt.BVSlice(b, 3, 3)))
    )
  }

  "analyze" should "return an updated mask and constraints / mappings" in {
    val lhs = smt.BVSymbol("lhs", 7)
    val arg = smt.BVSymbol("arg", 32)
    def ana(old: BigInt) = BitMapping.analyze(old, lhs, arg, 10, 4)

    {
      val (const, map, mask) = ana(BigInt("0", 2))
      assert(mask == BigInt("11111110000", 2))
      assert(const == smt.True())
      assert(simplify(map) == smt.BVEqual(lhs, smt.BVSlice(arg, 10, 4)))
    }
  }
}
