// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>
package paso

import chisel3.RawModule


class VerificationPlan {

}


object VerificationPlan {
  def randomTest[M <: RawModule](impl: => M)(spec: M => ProtocolSpec, samples: Int): VerificationPlan = ???
  def boundedCheck[M <: RawModule](impl: => M, spec: M => ProtocolSpec, bound: Int): VerificationPlan = ???
  def inductiveProof[M <: RawModule](impl: => M, spec: M => ProtocolSpec, invariances: (M, ProtocolSpec) => ???): VerificationPlan = ???
}
