// Copyright 2020 The Regents of the University of California
// Copyright 2020, SiFive, Inc
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso

import chisel3._
import chisel3.experimental.{ChiselAnnotation, annotate}
import firrtl.annotations.{ModuleTarget, SingleTargetAnnotation}
import paso.untimed.{ElaborateUntimed, Method, MethodParent, NMethodBuilder}

import scala.collection.mutable

class UntimedModule extends MultiIOModule with MethodParent {
  override def addMethod(m: Method): Unit = _methods.append(m)
  override def getName: String = this.pathName
  override def isElaborated: Boolean =_isElaborated
  private[paso] var _isElaborated = false
  private val _methods = mutable.ArrayBuffer[Method]()
  private val methodNames = mutable.HashSet[String]()
  def methods: Seq[Method] = _methods
  // TODO: automagically infer names like Chisel does for its native constructs
  def fun(name: String) = {
    require(!methodNames.contains(name), s"Method $name already exists")
    methodNames += name
    NMethodBuilder(this, name)
  }
}

object UntimedModule {
  def apply[M <: UntimedModule](m: => M): M = {
    val sub = Module(m)
    annotate(new ChiselAnnotation { override def toFirrtl = SubmoduleAnnotation(sub.toTarget, sub) })
    sub
  }
  def elaborate[M <: UntimedModule](m: => M): M = {
    ElaborateUntimed(m)
  }
}

case class SubmoduleAnnotation(target: ModuleTarget, untimed: UntimedModule) extends SingleTargetAnnotation[ModuleTarget] {
  def duplicate(n: ModuleTarget) = this.copy(n)
}