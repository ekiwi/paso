// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso

import chisel3.RawModule
import firrtl.annotations.ModuleTarget
import paso.chisel.Elaboration
import paso.verification.VerificationProblem

import scala.collection.mutable

abstract class SubSpecs[I <: RawModule](val impl: I) {
  trait IsSubmodule { def getTarget: ModuleTarget ; def getSpec: ProtocolSpec[UntimedModule] ; val instancePath: String }
  case class Submodule[I <: RawModule, S <: UntimedModule](instancePath: String, impl: I, spec: I => ProtocolSpec[S], var bindings: Seq[UntimedModule] = Seq()) extends IsSubmodule {
    override def getTarget: ModuleTarget = impl.toTarget
    override def getSpec: ProtocolSpec[UntimedModule] = spec(impl)
    /** marks a RTL submodule as implementing an untimed submodule */
    def bind(untimed: UntimedModule): Unit = { bindings = bindings ++ Seq(untimed) }
  }
  val subspecs = mutable.ArrayBuffer[IsSubmodule]() // modules that should be abstracted by replacing them with their spec

  /** marks a submodule to be replaced with its specification */
  def replace[I <: RawModule, S <: UntimedModule](module: I)(spec: I => ProtocolSpec[S]): Unit = {
    subspecs.append(Submodule(module.pathName, module, spec))
  }
}

case class NoSubSpecs[I <: RawModule](override val impl: I) extends SubSpecs[I](impl) {}

case class PasoImpl[I <: RawModule](impl: () => I) {
  def apply[S <: UntimedModule](spec: I => ProtocolSpec[S]): PasoImplAndSpec[I,S] = PasoImplAndSpec(impl, spec)
}

case class PasoImplAndSpec[I <: RawModule, S <: UntimedModule](impl: () => I, spec: I => ProtocolSpec[S]) {
  def proof(): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_), NoProofCollateral(_, _))
  def proof(inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_), inv)
  def bmc(k: Int): Boolean = Paso.runBmc[I,S](impl, spec, NoSubSpecs(_), k)
  def randomTest(k: Int): Boolean = Paso.runRandomTest[I,S](impl, spec, new NoSubSpecs(_), k)
  def apply(subspecs: I => SubSpecs[I]): PasoImplAndSpecAndSubspecs[I,S] = PasoImplAndSpecAndSubspecs(impl, spec, subspecs)
}

case class PasoImplAndSpecAndSubspecs[I <: RawModule, S <: UntimedModule](impl: () => I, spec: I => ProtocolSpec[S], subspecs: I => SubSpecs[I]) {
  def proof(): Boolean = Paso.runProof[I,S](impl, spec, subspecs, NoProofCollateral(_, _))
  def proof(inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, subspecs, inv)
  def bmc(k: Int): Boolean = Paso.runBmc[I,S](impl, spec, subspecs, k)
  def randomTest(k: Int): Boolean = Paso.runRandomTest[I,S](impl, spec, subspecs, k)
}

object Paso {
  def apply[I <: RawModule](impl: => I): PasoImpl[I] = PasoImpl(() => impl)

  private[paso] def runProof[I <: RawModule, S <: UntimedModule](impl: () => I, spec: I => ProtocolSpec[S], subspecs: I => SubSpecs[I], inv: (I, S) => ProofCollateral[I,S]): Boolean = {
    val elaborated = Elaboration()[I, S](impl, spec, subspecs, inv)
    VerificationProblem.verify(elaborated)
    true
  }
  private[paso] def runBmc[I <: RawModule, S <: UntimedModule](impl: () => I, spec: I => ProtocolSpec[S], subspecs: I => SubSpecs[I], k: Int): Boolean = ???
  private[paso] def runRandomTest[I <: RawModule, S <: UntimedModule](impl: () => I, spec: I => ProtocolSpec[S], subspecs: I => SubSpecs[I], k: Int): Boolean = ???
}