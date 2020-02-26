// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

// contains data structures used for verification
// mostly language neutral (aka Chisel independent)

package paso
import uclid.smt

// case class UntimedModel(name: String, state: Map[String, ???])

// things that need to be verified:
// (1) do assertions on untimed model always hold? (can we do an inductive proof?)
// (2) do the invariances over the implementation hold after a reset?
// (3) check the base case for the mapping function (see MC 11.1 and Definition 13.2):
//     3.1) for all initial states in the untimed model, there exists a state in the
//          timed model and that state is pan initial state
//     TODO
// (4)



case class UntimedMethod(name: String, inputs: Map[String,smt.Type], outputs: Map[String,smt.Type],
                         guard: smt.Expr, sem: Map[String, smt.Expr])
case class UntimedModel(name: String, methods: Seq[UntimedMethod], state: Seq[smt.Symbol])
case class Protocol()

case class VerificationProblem(
  impl: smt.SymbolicTransitionSystem,
  untimed: UntimedModule,



)
