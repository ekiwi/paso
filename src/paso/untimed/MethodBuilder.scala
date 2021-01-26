// Copyright 2020 The Regents of the University of California
// Copyright 2020, SiFive, Inc
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.untimed
import chisel3._

case class NMethodBuilder(p: MethodParent, n: String, guard: List[() => Bool] = List()) {
  def in[I <: Data](inputType: I): IMethodBuilder[I] = IMethodBuilder(p, n, inputType, guard)
  def out[O <: Data](outputType: O): OMethodBuilder[O] = OMethodBuilder(p, n, outputType, guard)
  def when(cond: => Bool): NMethodBuilder = { this.copy(guard = this.guard :+ (() => cond))}
  def apply(impl: => Unit): NMethod = {
    val g = MethodBuilder.mergeGuard(guard)
    val m = NMethod(n, g, () => impl, p) ; p.addMethod(m) ; m
  }
}
case class OMethodBuilder[O <: Data](p: MethodParent, n: String, outputType: O, guard: List[() => Bool] = List()) {
  def when(cond: => Bool): OMethodBuilder[O] = { this.copy(guard = this.guard :+ (() => cond))}
  def apply(impl: O => Unit): OMethod[O] = {
    val g = MethodBuilder.mergeGuard(guard)
    val m = OMethod(n, g, outputType, impl, p) ; p.addMethod(m) ; m
  }
}
case class IMethodBuilder[I <: Data](p: MethodParent, n : String, inputType: I, guard: List[() => Bool] = List()) {
  def out[O <: Data](outputType: O): IOMethodBuilder[I, O] = IOMethodBuilder(p, n, inputType, outputType, guard)
  def when(cond: => Bool): IMethodBuilder[I] = { this.copy(guard = this.guard :+ (() => cond))}
  def apply(impl: I => Unit): IMethod[I] = {
    val g = MethodBuilder.mergeGuard(guard)
    val m = IMethod(n, g, inputType, impl, p) ; p.addMethod(m) ; m
  }
}
case class IOMethodBuilder[I <: Data, O <: Data](p: MethodParent, n: String, inputType: I, outputType: O, guard: List[() => Bool] = List()) {
  def when(cond: => Bool): IOMethodBuilder[I,O] = { this.copy(guard = this.guard :+ (() => cond))}
  def apply(impl: (I, O) => Unit): IOMethod[I,O] = {
    val g = MethodBuilder.mergeGuard(guard)
    val m = IOMethod(n, g, inputType, outputType, impl, p) ; p.addMethod(m) ; m
  }
}

private object MethodBuilder {
  def mergeGuard[D <: Data](guard: List[() => Bool]): () => Bool = {
    if(guard.isEmpty) {
      () => true.B
    } else if(guard.size == 1) {
      guard.head
    } else {
      () => guard.foldLeft(guard.head())((a,b) => a && b())
    }
  }
}