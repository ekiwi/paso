// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

// contains data structures used for verification
// mostly language neutral (aka Chisel independent)

package paso.verification

import uclid.smt

// things that need to be verified:
// (1) do assertions on untimed model always hold? (can we do an inductive proof?)
// (2) do the invariances over the implementation hold after a reset?
// (3) check the base case for the mapping function (see MC 11.1 and Definition 13.2):
//     3.1) for all initial states in the untimed model, there exists a state in the
//          timed model and that state is pan initial state
//     TODO
// (4)

// Verification Graph
case class PendingInputNode(next: Seq[InputEdge] = Seq())
case class PendingOutputNode(next: Seq[OutputEdge] = Seq())
case class InputEdge(I: Seq[smt.Expr] = Seq(), A: Seq[smt.Expr] = Seq(), next: Option[PendingOutputNode] = None)
case class OutputEdge(O: Seq[smt.Expr] = Seq(), R: Seq[smt.Expr] = Seq(), next: Option[PendingInputNode] = None)

case class Assertion(guard: smt.Expr, pred: smt.Expr)

case class VerificationProblem(
  impl: smt.SymbolicTransitionSystem,
  untimed: UntimedModel,
  protocols: Map[String, PendingInputNode],
  invariances: Seq[Assertion],
  mapping: Seq[Assertion]
)
