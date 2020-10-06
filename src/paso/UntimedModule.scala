// Copyright 2020 The Regents of the University of California
// Copyright 2020, SiFive, Inc
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso

import chisel3._
import paso.untimed._

import scala.collection.mutable

class UntimedModule extends MultiIOModule with MethodParent {
  override private[paso] def addMethod(m: Method): Unit = _methods.append(m)
  override def isElaborated: Boolean =_isElaborated
  private var _isElaborated = false
  private val _methods = mutable.ArrayBuffer[Method]()
  private var _chirrtl: Option[firrtl.CircuitState] = None
  private lazy val _lowfir = UntimedCompiler.run(_chirrtl.get, Set())
  private lazy val _tester = UntimedCompiler.toTreadleTester(_chirrtl.get)
  private val methodNames = mutable.HashSet[String]()
  def getFirrtl: firrtl.CircuitState = {
    assert(_isElaborated, "You need to elaborate the module using UntimedModule(new ...)!")
    _lowfir
  }
  def getTester: treadle.TreadleTester = {
    assert(_isElaborated, "You need to elaborate the module using UntimedModule(new ...)!")
    _tester
  }
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
      val sub = Module {
        val em = m
        // generate the circuit for each method
        em.methods.foreach(_.generate())
        em
      }
      sub
    } else { // but it can also be used to elaborate the toplevel
      elaborate(m)
    }
  }
  def elaborate[M <: UntimedModule](m: => M): M = {
    elaborating.set(true)
    val gen = () => {
      val em = m
      // generate the circuit for each method
      em.methods.foreach(_.generate())
      em
    }
    val (fir, mod) = ChiselCompiler.elaborate(gen)

    mod._isElaborated = true
    mod._chirrtl = Some(fir)
    elaborating.set(false)
    mod
  }
}