// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package sha3

import chisel3._
import paso._

/**
 * SHA3 spec based on
 * - MIT licensed https://github.com/mjosaarinen/tiny_sha3
 * - https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
 * */
class SHA3Spec extends UntimedModule {

  val rndc = Seq(
    "h0000000000000001".U, "h0000000000008082".U, "h800000000000808a".U,
    "h8000000080008000".U, "h000000000000808b".U, "h0000000080000001".U,
    "h8000000080008081".U, "h8000000000008009".U, "h000000000000008a".U,
    "h0000000000000088".U, "h0000000080008009".U, "h000000008000000a".U,
    "h000000008000808b".U, "h800000000000008b".U, "h8000000000008089".U,
    "h8000000000008003".U, "h8000000000008002".U, "h8000000000000080".U,
    "h000000000000800a".U, "h800000008000000a".U, "h8000000080008081".U,
    "h8000000000008080".U, "h0000000080000001".U, "h8000000080008008".U)

  val rotc = Seq(
    1,  3,  6,  10, 15, 21, 28, 36, 45, 55, 2,  14,
    27, 41, 56, 8,  25, 43, 62, 18, 39, 61, 20, 44)

  val piln = Seq(
    10, 7,  11, 17, 18, 3, 5,  16, 8,  21, 24, 4,
    15, 23, 19, 13, 12, 2, 20, 14, 22, 9,  6,  1)

  def rotateLeft(u: UInt, by: Int): UInt = {
    val w = u.getWidth
    val offset = by % w
    if(offset == 0) { u } else {
      u(w - 1 - offset, 0) ## u(w - 1, w - offset)
    }
  }

  // in the style of the NIST spec
  type State = Seq[Seq[UInt]]
  def thetaNist(A: State): State = {
    val C = (0 until 5).map(x => A(x)(0) ^ A(x)(1) ^ A(x)(2) ^ A(x)(3) ^ A(x)(4))
    val D = (0 until 5).map(x => C((x - 1) % 5) ^ rotateLeft(C((x + 1) % 5), 1))
    A.zipWithIndex.map{ case (ax, x) => ax.map(ay => ay ^ D(x))}
  }

  def theta(st: Seq[UInt]): Seq[UInt] = {
    val bc = (0 until 5).map(i => st(i) ^ st(i + 5) ^ st(i + 10) ^ st(i + 15) ^ st(i + 15))
    val t = (0 until 5).map(i => bc((i + 4) % 5) ^ rotateLeft(bc((i + 1) % 5), 1))
    st.zipWithIndex.map{ case (s, j) => s ^ t(j % 5) }
  }

  def rho(st: Seq[UInt]): Seq[UInt] = {
    var t = st(1)
    piln.zip(rotc).map { case (j, rotc_i) =>
      val bc_0 = st(j)
      val st_j = rotateLeft(t, rotc_i)
      t = bc_0
      (j, st_j)
    }.sortBy(_._1).map(_._2)
  }

  def chi(st: Seq[UInt]): Seq[UInt] = {
    def bc(i: Int, j: Int): UInt = {
      val base = (j / 5) * 5
      st(base + (i % 5))
    }
    st.zipWithIndex.map { case (s, j) =>
      val i = j % 5
      s ^ (~bc(j + 1, j) & bc(j + 2, j))
    }
  }

  def keccakfRound(r: Int, st: Seq[UInt]): Seq[UInt] = {
    val nextSt = chi(rho(theta(st)))
    val s0 = nextSt.head ^ rndc(r)
    Seq(s0) ++ nextSt.drop(1)
  }

  def keccakf(state: Seq[UInt]): Seq[UInt] = {
    require(state.length == 25, "Only support 5 x 5 x 64bit version")
    (0 until 8).foldLeft(state){ case(st, r) => keccakfRound(r, st) }
  }

}
