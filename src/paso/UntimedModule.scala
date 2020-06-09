// Copyright 2020 The Regents of the University of California
// Copyright 2020, SiFive, Inc
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso

import chisel3._
import chisel3.experimental.{ChiselAnnotation, annotate}
import firrtl.annotations.{ModuleTarget, SingleTargetAnnotation}
import paso.chisel.ChiselCompiler
import paso.untimed._

import scala.collection.mutable

class UntimedModule extends MultiIOModule with MethodParent {
  override private[paso] def addMethod(m: Method): Unit = _methods.append(m)
  override def getName: String = this.pathName
  override def isElaborated: Boolean =_isElaborated
  private var _isElaborated = false
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
  private val elaborating = new ThreadLocal[Boolean] { override def initialValue(): Boolean = false }
  def apply[M <: UntimedModule](m: => M): M = {
    // when elaborating, this acts like chisel3.Module(...)
    if(elaborating.get()) {
      val sub = Module(m)
      annotate(new ChiselAnnotation { override def toFirrtl = SubmoduleAnnotation(sub.toTarget, sub) })
      sub
    } else { // but it can also be used to elaborate the toplevel
      elaborate(m)
    }
  }
  def elaborate[M <: UntimedModule](m: => M): M = {
    elaborating.set(true)
    var opt: Option[M] = None
    val gen = () => {
      opt = Some(m)
      // generate the circuit for each method
      opt.get.methods.foreach(_.generate())
      opt.get
    }
    val fir = ChiselCompiler.elaborate(gen)
    val mod = opt.get
    mod._isElaborated = true
    elaborating.set(false)
    mod
  }
}

case class SubmoduleAnnotation(target: ModuleTarget, untimed: UntimedModule) extends SingleTargetAnnotation[ModuleTarget] {
  def duplicate(n: ModuleTarget) = this.copy(n)
}