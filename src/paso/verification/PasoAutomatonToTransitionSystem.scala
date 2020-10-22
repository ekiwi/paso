// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import maltese.smt
import paso.protocols.PasoAutomaton

/** Turns the PasoAutomaton into a TransitionSystem which can then be combined with the Design Under Verification
 *  for bounded model checking or inductive proofs.
 */
object PasoAutomatonToTransitionSystem {
  def apply(auto: PasoAutomaton): smt.TransitionSystem = {




    ???
  }
}
