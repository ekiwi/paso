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
trait VerificationEdge { val methods: Set[String] ; val next: VerificationNode }
trait VerificationNode { val next: Seq[VerificationEdge] }
case class PendingInputNode(next: Seq[InputEdge] = Seq()) extends VerificationNode
case class PendingOutputNode(next: Seq[OutputEdge] = Seq()) extends VerificationNode
case class InputEdge(constraints: Seq[smt.Expr] = Seq(), mappings: Seq[smt.Expr] = Seq(), methods: Set[String], next: PendingOutputNode) extends VerificationEdge
case class OutputEdge(constraints: Seq[smt.Expr] = Seq(), mappings: Seq[smt.Expr] = Seq(), methods: Set[String], next: PendingInputNode) extends VerificationEdge

case class Assertion(guard: smt.Expr, pred: smt.Expr)

case class VerificationProblem(
  impl: smt.SymbolicTransitionSystem,
  untimed: UntimedModel,
  protocols: Map[String, PendingInputNode],
  invariances: Seq[Assertion],
  mapping: Seq[Assertion]
)
