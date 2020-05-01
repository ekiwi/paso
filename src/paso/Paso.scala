// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso

import chisel3.RawModule
import firrtl.annotations.{ModuleTarget, ReferenceTarget}

import scala.collection.mutable

object Paso {

}

sealed trait IsSpec {}
case class SubSpec[M <: RawModule](target: ModuleTarget, genSpec: M => ProtocolSpec) extends  IsSpec
trait SpecGenerator { def apply(impl: RawModule): ProtocolSpec }

trait VerificationTask[M <: RawModule] {
  def impl: M
  def spec(impl: M): ProtocolSpec
  def subspecs(impl: M): Seq[SubSpec] = Seq()
}


class SubspecBindings {
  val subspecs = mutable.ArrayBuffer[IsSpec]()

  def replace[M <: RawModule](module: M)(spec: M => ProtocolSpec): Unit = {
    subspecs.append(SubSpec(module.toTarget, spec))
  }
  def bind[M <: RawModule](module: M, untimed: UntimedModule, spec: M => ProtocolSpec): Unit = {

  }
}