// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso

import chisel3.RawModule
import firrtl.annotations.ModuleTarget
import paso.chisel.Elaboration
import paso.verification.VerificationProblem

import scala.collection.mutable

trait IsSubmodule { val makeSpec: () => ProtocolSpec[UntimedModule] ; val instancePath: String ; def getBinding: Option[String] }

abstract class SubSpecs[IM <: RawModule, SM <: UntimedModule](val impl: IM, val spec: SM) {
  case class Submodule[I <: RawModule, S <: UntimedModule](instancePath: String, impl: I, spec: I => ProtocolSpec[S], var binding: Option[String] = None) extends IsSubmodule {
    override val makeSpec = () => spec(impl)
    override def getBinding: Option[String] = binding
    /** marks a RTL submodule as implementing an untimed submodule */
    def bind(untimed: S): Unit = {
      assert(binding.isEmpty)
      binding = Some(untimed.instanceName)
    }
  }
  val subspecs = mutable.ArrayBuffer[IsSubmodule]() // modules that should be abstracted by replacing them with their spec

  /** marks a submodule to be replaced with its specification */
  def replace[I <: RawModule, S <: UntimedModule](module: I)(spec: I => ProtocolSpec[S]): Submodule[I,S] = {
    val name = module.pathName.split('.').drop(1).mkString(".")
    val sub = Submodule(name, module, spec)
    subspecs.append(sub)
    sub
  }
}

case class NoSubSpecs[I <: RawModule, S <: UntimedModule](override val impl: I, override val spec: S) extends SubSpecs[I,S](impl, spec) {}

case class PasoImpl[I <: RawModule](impl: () => I) {
  def apply[S <: UntimedModule](spec: I => ProtocolSpec[S]): PasoImplAndSpec[I,S] = PasoImplAndSpec(impl, spec)
}

case class PasoImplAndSpec[I <: RawModule, S <: UntimedModule](impl: () => I, spec: I => ProtocolSpec[S]) {
  def proof(): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_, _), NoProofCollateral(_, _))
  def proof(inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_, _), inv)
  def proof(opt: ProofOptions): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_, _), NoProofCollateral(_, _), opt)
  def proof(opt: ProofOptions, inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_, _), inv, opt)
  def bmc(k: Int): Boolean = Paso.runBmc[I,S](impl, spec, NoSubSpecs(_, _), k)
  def randomTest(k: Int): Boolean = Paso.runRandomTest[I,S](impl, spec, new NoSubSpecs(_, _), k)
  def apply(subspecs: (I, S) => SubSpecs[I,S]): PasoImplAndSpecAndSubspecs[I,S] = PasoImplAndSpecAndSubspecs(impl, spec, subspecs)
}

case class PasoImplAndSpecAndSubspecs[I <: RawModule, S <: UntimedModule](impl: () => I, spec: I => ProtocolSpec[S], subspecs: (I, S) => SubSpecs[I, S]) {
  def proof(): Boolean = Paso.runProof[I,S](impl, spec, subspecs, NoProofCollateral(_, _))
  def proof(inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, subspecs, inv)
  def proof(opt: ProofOptions): Boolean = Paso.runProof[I,S](impl, spec, subspecs, NoProofCollateral(_, _), opt)
  def proof(opt: ProofOptions, inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, subspecs, inv, opt)
  def bmc(k: Int): Boolean = Paso.runBmc[I,S](impl, spec, subspecs, k)
  def randomTest(k: Int): Boolean = Paso.runRandomTest[I,S](impl, spec, subspecs, k)
}

object Paso {
  def apply[I <: RawModule](impl: => I): PasoImpl[I] = PasoImpl(() => impl)

  private[paso] def runProof[I <: RawModule, S <: UntimedModule](impl: () => I, spec: I => ProtocolSpec[S], subspecs: (I, S) => SubSpecs[I, S], inv: (I, S) => ProofCollateral[I,S], opt: ProofOptions = Default): Boolean = {
    // warm up
    val elaborated1 = Elaboration()[I, S](impl, spec, subspecs, inv)
    val elaborated2 = Elaboration()[I, S](impl, spec, subspecs, inv)
    // actual time
    val elaborated = Elaboration()[I, S](impl, spec, subspecs, inv)
    VerificationProblem.verify(elaborated, opt)
    true
  }
  private[paso] def runBmc[I <: RawModule, S <: UntimedModule](impl: () => I, spec: I => ProtocolSpec[S], subspecs: (I, S) => SubSpecs[I,S], kMax: Int, opt: ProofOptions = Default): Boolean = {
    val elaborated = Elaboration()[I, S](impl, spec, subspecs, NoProofCollateral(_, _))
    VerificationProblem.bmc(elaborated, opt.modelChecker, kMax)
    true
  }
  private[paso] def runRandomTest[I <: RawModule, S <: UntimedModule](impl: () => I, spec: I => ProtocolSpec[S], subspecs: (I, S) => SubSpecs[I,S], k: Int): Boolean = ???

  val MCBotr = ProofOptions(CVC4, Btormc)
  val MCYices2 = ProofOptions(CVC4, Yices2)
  val MCCVC4 = ProofOptions(CVC4, CVC4)
  val MCZ3 = ProofOptions(CVC4, Z3)
  val Default = MCBotr
}

sealed trait SolverName
case object CVC4 extends SolverName
case object Yices2 extends SolverName
case object Btormc extends SolverName
case object Z3 extends SolverName

case class ProofOptions(baseCaseSolver: SolverName, modelChecker: SolverName, oneMethodAtATime: Boolean = true, checkSimplifications: Boolean = false)