// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>
package paso

import chisel3._
import chisel3.experimental.{ChiselAnnotation, IO, annotate}
import chisel3.util.log2Ceil
import firrtl.annotations.{ReferenceTarget, SingleTargetAnnotation}

import scala.collection.mutable


abstract class ProofCollateral[I <: RawModule, S <: UntimedModule](impl: I, spec: S) {

  val invs = new mutable.ArrayBuffer[I => Unit]()
  def invariants(gen: I => Unit): Unit = invs.append(gen)


  val maps = new mutable.ArrayBuffer[(I,S) => Unit]()
  def mapping(gen: (I, S) => Unit): Unit = maps.append(gen)

  // replace default chisel assert
  def assert(cond: => Bool): Unit = {
    chisel3.experimental.verification.assert(cond)
  }

  implicit class comparableMem[T <: UInt](x: Mem[T]) {
    def ===(y: Mem[T]): Bool = {
      require(x.length > 0)
      require(x.length == y.length)
      val w = Wire(Bool()).suggestName(s"eq($x, $y)")
      dontTouch(w)
      val depth = x.length
      val width = x.t.getWidth
      annotate(new ChiselAnnotation { override def toFirrtl = MemEqualAnnotation(w.toTarget, x.toTarget, y.toTarget, depth, width) })
      w
    }
  }

  private val forallNames = mutable.HashSet[String]()
  private val variableLetters = List("i", "j", "k", "l", "m", "n")
  private def getUniqueForallIOName(range: Range): String = {
    // s"ii_${range.start}_to_${range.end-1}"
    val names = variableLetters
    val name = names.iterator.filterNot(forallNames).next()
    forallNames.add(name)
    name
  }

  def forall(range: Range)(block: UInt => Unit): Unit = {
    require(range.step == 1, s"Only step size 1 supported: $range")
    require(range.start >= 0 && range.end >= 0, s"Only positive ranges supported: $range")
    require(range.start <= range.end)

    // generate a wire to represent the universally quantified variable
    val bits = log2Ceil(range.end)
    // TODO: ensure unique name for the IO

    val ii = IO(Input(UInt(bits.W))).suggestName(getUniqueForallIOName(range))
    annotate(new ChiselAnnotation { override def toFirrtl = ForallAnnotation(ii.toTarget, bits, range.start, range.end) })

    // generate the block code once
    block(ii)
  }
}

case class NoProofCollateral[I <: RawModule, S <: UntimedModule](impl: I, spec: S) extends ProofCollateral(impl, spec)

case class MemToVecAnnotation(target: ReferenceTarget, mem: ReferenceTarget, depth: BigInt, width: Int) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}

case class MemEqualAnnotation(target: ReferenceTarget, mem0: ReferenceTarget, mem1: ReferenceTarget, depth: BigInt, width: Int) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}

case class ForallAnnotation(target: ReferenceTarget, width: Int, start: Int, end: Int) extends SingleTargetAnnotation[ReferenceTarget] {
  def duplicate(n: ReferenceTarget) = this.copy(n)
}