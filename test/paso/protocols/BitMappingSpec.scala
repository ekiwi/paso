// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

import org.scalatest.flatspec.AnyFlatSpec

class BitMappingSpec extends AnyFlatSpec {
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
}
