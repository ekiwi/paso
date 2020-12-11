// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.smt.solvers

import org.scalatest.flatspec.AnyFlatSpec

class SMTLibResponseParserSpec extends AnyFlatSpec {
  behavior of "SMTLibResponseParser"

  def in(value: String): String = s"((in $value))"

  it should "parse an array with default value in binary" in {
    val array = "((as const (Array (_ BitVec 5) (_ BitVec 32))) #b00000000000000000000000000110011)"
    val expected = Seq((None, BigInt(0x33)))
    assert(SMTLibResponseParser.parseMemValue(in(array)) == expected)
  }

  private val base = "((as const (Array (_ BitVec 5) (_ BitVec 32))) #x00000033)"

  it should "parse an array with default value in hex" in {
    val expected = Seq((None, BigInt(0x33)))
    assert(SMTLibResponseParser.parseMemValue(in(base)) == expected)
  }

  private val store = s"(store $base #b01110 #x00000000)"

  it should "parse a store" in {
    val expected = Seq((None, BigInt(0x33)), (Some(BigInt(0xe)), BigInt(0)))
    assert(SMTLibResponseParser.parseMemValue(in(store)) == expected)
  }

  it should "parse a two stores" in {
    val store2 = s"(store $store #b01110 #x00000011)"
    val expected = Seq((None, BigInt(0x33)), (Some(BigInt(0xe)), BigInt(0)), (Some(BigInt(0xe)), BigInt(0x11)))
    assert(SMTLibResponseParser.parseMemValue(in(store2)) == expected)
  }

  // Z3 uses lets when doing multiple stores
  it should "parse a let" in {
    val innerStore = s"(store a!1 #b01110 #x00000011)"
    val letA1 = s"(let ((a!1 $store)) $innerStore)"
    val expected = Seq((None, BigInt(0x33)), (Some(BigInt(0xe)), BigInt(0)), (Some(BigInt(0xe)), BigInt(0x11)))
    assert(SMTLibResponseParser.parseMemValue(in(letA1)) == expected)
  }


}
