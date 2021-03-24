// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso

import chisel3.RawModule
import firrtl.annotations.{InstanceTarget, ModuleTarget}
import paso.chisel.Elaboration
import paso.formal.VerificationProblem
import paso.random.TestingProblem

import java.nio.file.Paths
import scala.collection.mutable

trait IsSubmodule {
  val makeSpec: () => ProtocolSpec[UntimedModule]
  val module: ModuleTarget
  def getBinding: Option[InstanceTarget]
}

abstract class SubSpecs[IM <: RawModule, SM <: UntimedModule](val impl: IM, val spec: SM) {
  case class Submodule[I <: RawModule, S <: UntimedModule](module: ModuleTarget, impl: I, spec: I => ProtocolSpec[S], var binding: Option[InstanceTarget] = None) extends IsSubmodule {
    override val makeSpec = () => spec(impl)
    override def getBinding: Option[InstanceTarget] = binding
    /** marks a RTL submodule as implementing an untimed submodule */
    def bind(untimed: S): Unit = {
      assert(binding.isEmpty)
      val ref = untimed.toAbsoluteTarget.asInstanceOf[InstanceTarget]
      binding = Some(ref)
    }
  }
  val subspecs = mutable.ArrayBuffer[IsSubmodule]() // modules that should be abstracted by replacing them with their spec

  /** marks a submodule to be replaced with its specification */
  def replace[I <: RawModule, S <: UntimedModule](module: I)(spec: I => ProtocolSpec[S]): Submodule[I,S] = {
    val sub = Submodule(module.toTarget, module, spec)
    subspecs.append(sub)
    sub
  }
}

case class NoSubSpecs[I <: RawModule, S <: UntimedModule](override val impl: I, override val spec: S) extends SubSpecs[I,S](impl, spec) {}

case class PasoImpl[I <: RawModule](impl: () => I, getTestDir: () => String) {
  def apply[S <: UntimedModule](spec: I => ProtocolSpec[S]): PasoImplAndSpec[I,S] = PasoImplAndSpec(this, spec)
}

case class PasoImplAndSpec[I <: RawModule, S <: UntimedModule](impl: PasoImpl[I], spec: I => ProtocolSpec[S]) {
  def proof(): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_, _), NoProofCollateral(_, _))
  def proof(inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_, _), inv)
  def proof(opt: ProofOptions, dbg: DebugOptions): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_, _), NoProofCollateral(_, _), opt, dbg)
  def proof(opt: ProofOptions): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_, _), NoProofCollateral(_, _), opt)
  def proof(opt: ProofOptions, inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_, _), inv, opt)
  def proof(opt: ProofOptions, dbg: DebugOptions, inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, NoSubSpecs(_, _), inv, opt, dbg)
  def bmc(k: Int): Boolean = Paso.runBmc[I,S](impl, spec, NoSubSpecs(_, _), k)
  def bmc(opt: ProofOptions, k: Int): Boolean = Paso.runBmc[I,S](impl, spec, NoSubSpecs(_, _), k, opt)
  def bmc(opt: ProofOptions, dbg: DebugOptions, k: Int): Boolean = Paso.runBmc[I,S](impl, spec, NoSubSpecs(_, _), k, opt, dbg)
  def randomTest(k: Int, recordWaveform: Boolean = false, seed: Option[Long] = Some(0)): Boolean = Paso.runRandomTest[I,S](impl, spec, k, recordWaveform, seed)
  def apply(subspecs: (I, S) => SubSpecs[I,S]): PasoImplAndSpecAndSubspecs[I,S] = PasoImplAndSpecAndSubspecs(impl, spec, subspecs)
}

case class PasoImplAndSpecAndSubspecs[I <: RawModule, S <: UntimedModule](impl: PasoImpl[I], spec: I => ProtocolSpec[S], subspecs: (I, S) => SubSpecs[I, S]) {
  def proof(): Boolean = Paso.runProof[I,S](impl, spec, subspecs, NoProofCollateral(_, _))
  def proof(inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, subspecs, inv)
  def proof(opt: ProofOptions): Boolean = Paso.runProof[I,S](impl, spec, subspecs, NoProofCollateral(_, _), opt)
  def proof(opt: ProofOptions, dbg: DebugOptions): Boolean = Paso.runProof[I,S](impl, spec, subspecs, NoProofCollateral(_, _), opt, dbg)
  def proof(opt: ProofOptions, inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, subspecs, inv, opt)
  def proof(opt: ProofOptions, dbg: DebugOptions, inv: (I, S) => ProofCollateral[I,S]): Boolean = Paso.runProof[I,S](impl, spec, subspecs, inv, opt, dbg)
  def bmc(k: Int): Boolean = Paso.runBmc[I,S](impl, spec, subspecs, k)
  def bmc(opt: ProofOptions, k: Int): Boolean = Paso.runBmc[I,S](impl, spec, subspecs, k, opt)
  def bmc(opt: ProofOptions, dbg: DebugOptions, k: Int): Boolean = Paso.runBmc[I,S](impl, spec, subspecs, k, opt, dbg)
  // random tests do not support suspects ATM
  //def randomTest(k: Int): Boolean = Paso.runRandomTest[I,S](impl, spec, subspecs, k)
}

object Paso {
  private[paso] def runProof[I <: RawModule, S <: UntimedModule](impl: PasoImpl[I], spec: I => ProtocolSpec[S], subspecs: (I, S) => SubSpecs[I, S], inv: (I, S) => ProofCollateral[I,S], opt: ProofOptions = Default, dbg: DebugOptions = NoDebug): Boolean = {
    val workingDir = impl.getTestDir()
    val elaborated = Elaboration(dbg, workingDir)[I, S](impl.impl, spec, subspecs, inv)
    VerificationProblem.verify(elaborated, opt, dbg, Paths.get(workingDir))
    true
  }
  private[paso] def runBmc[I <: RawModule, S <: UntimedModule](impl: PasoImpl[I], spec: I => ProtocolSpec[S], subspecs: (I, S) => SubSpecs[I,S], kMax: Int, opt: ProofOptions = Default, dbg: DebugOptions = NoDebug): Boolean = {
    val workingDir = impl.getTestDir()
    val elaborated = Elaboration(dbg, workingDir)[I, S](impl.impl, spec, subspecs, NoProofCollateral(_, _))
    VerificationProblem.bmc(elaborated, opt.modelChecker, kMax, dbg, Paths.get(workingDir))
    true
  }
  private[paso] def runRandomTest[I <: RawModule, S <: UntimedModule](impl: PasoImpl[I], spec: I => ProtocolSpec[S], kMax: Int, recordWaveform: Boolean, seed: Option[Long], dbg: DebugOptions = NoDebug): Boolean = {
    val workingDir = impl.getTestDir()
    val elaborated = Elaboration(dbg, workingDir).elaborateConcrete(impl.impl, spec, recordWaveform)
    TestingProblem.randomTest(elaborated, kMax, seed, dbg)
    true
  }

  val MCBotr = ProofOptions(Btormc)
  val MCYices2 = ProofOptions(Yices2)
  val MCCVC4 = ProofOptions(CVC4)
  val MCZ3 = ProofOptions(Z3)
  val MCUclid5 = ProofOptions(Uclid5)
  val Default = MCBotr
  val NoDebug = DebugOptions()
}

sealed trait SolverName
case object CVC4 extends SolverName
case object Yices2 extends SolverName
case object Btormc extends SolverName
case object Z3 extends SolverName
case object Uclid5 extends SolverName

case class ProofOptions(
  modelChecker: SolverName,
  oneMethodAtATime: Boolean = true,
  checkSimplifications: Boolean = false)

case class DebugOptions(
  // elaboration
  traceInvariantElaboration: Boolean = false,
  traceImplElaboration: Boolean = false,
  traceProtocolElaboration: Boolean = false,
  // verification
  printMCProgress: Boolean = false,
  printBaseSys: Boolean = false,
  printInductionSys: Boolean = false,
  printBmcSys: Boolean = false
)