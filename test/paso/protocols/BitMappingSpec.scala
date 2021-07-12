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

  "analyze" should "only return mappings if they actually exist" in {
    // this reproduces a bug, where the returned mapping would sometimes contain True elements
    val (src, dst) = (smt.BVSymbol("src", 5), smt.BVSymbol("dst", 5))
    val old = Map("src" -> BigInt(31), "dst" -> BigInt(31))
    val dataSym = smt.BVSymbol("data", 16)
    val assignment = Seq(smt.BVLiteral(3, 6), smt.BVSlice(src, 4, 4), dst, smt.BVSlice(src, 3, 0)).reduce(smt.BVConcat)

    val (constr, maps, updatedMappings) = BitMapping.analyze(old, dataSym, assignment)
    assert(maps.isEmpty, "All bits of src and dst are already mapped!")
    assert(updatedMappings == old, "The mapping should not change!")
    val c = constr.map(simplify)
    assert(c.head.toString() == "eq(data[15:10], 6'b11)")
    assert(c(1).toString() == "eq(data[9], src[4])")
    assert(c(2).toString() == "eq(data[8:4], dst)")
    assert(c(3).toString() == "eq(data[3:0], src[3:0])")
  }
}
