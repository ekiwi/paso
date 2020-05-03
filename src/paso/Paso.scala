// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso

import chisel3.RawModule
import firrtl.annotations.ModuleTarget
import paso.chisel.Elaboration
import paso.verification.VerificationProblem

import scala.collection.mutable

class SubspecBindings {
  val subspecs = mutable.ArrayBuffer[ModuleTarget]() // modules that should be abstracted by replacing them with their spec
  case class Binding(impl: ModuleTarget, spec: ModuleTarget)
  val bindings = mutable.ArrayBuffer[Binding]()

  /** marks a submodule to be replaced with its specification */
  def replace(module: RawModule): Unit = {
    subspecs.append(module.toTarget)
  }

  /** marks a RTL submodule as implementing an untimed submodule */
  def bind(module: RawModule, untimed: UntimedModule): Unit = {
    bindings.append(Binding(module.toTarget, untimed.toTarget))
  }
}

trait PasoVerificationTask { def run(): Boolean }
case class PasoVerificationProblem[I <: RawModule, S <: UntimedModule](impl: () => I, spec: I => ProtocolSpec[S])
case class PasoProof[I <: RawModule, S <: UntimedModule](p: PasoVerificationProblem[I, S], inv: (I, S) => ProofCollateral[I,S]) extends PasoVerificationTask {
  override def run(): Boolean = {
    val elaborated = Elaboration()[I, S](p.impl, p.spec, inv)
    VerificationProblem.verify(elaborated)
    true
  }
}

object Paso {
  def proof[I <: RawModule, S <: UntimedModule](impl: => I)(spec: I => ProtocolSpec[S])(inv: (I, S) => ProofCollateral[I,S]): PasoProof[I, S] =
    PasoProof(PasoVerificationProblem(() => impl, spec), inv)
}