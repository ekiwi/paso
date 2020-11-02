// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package maltese.mc

import maltese.smt
import scala.collection.mutable

case class SMTModelCheckerOptions(checkConstraints: Boolean, checkBadStatesIndividually: Boolean, simplify: Boolean)
object SMTModelCheckerOptions {
  val Default: SMTModelCheckerOptions = SMTModelCheckerOptions(true, true, false)
  val Performance: SMTModelCheckerOptions = SMTModelCheckerOptions(false, false, true)
}

/** SMT based bounded model checking as an alternative to dispatching to a btor2 based external solver */
class SMTModelChecker(val solver: smt.Solver, options: SMTModelCheckerOptions = SMTModelCheckerOptions.Default) extends IsModelChecker {
  override val name: String = "SMTModelChecker with " + solver.name
  override val supportsUF: Boolean = true
  override val supportsQuantifiers: Boolean = solver.supportsQuantifiers

  override def check(sys: TransitionSystem, kMax: Int, fileName: Option[String] = None): ModelCheckResult = {
    require(kMax > 0 && kMax <= 2000, s"unreasonable kMax=$kMax")
    if(fileName.nonEmpty) println("WARN: dumping to file is not supported at the moment.")

    // create new context
    solver.push()

    // declare/define functions and encode the transition system
    val enc: SMTEncoding = ??? // new CompactEncoding(sys, options.simplify)
    enc.defineHeader(solver)
    enc.init(solver)

    val constraints = sys.signals.filter(_.lbl == IsConstraint).map(_.name)
    val bads = sys.signals.filter(_.lbl == IsBad).map(_.name)

    (0 to kMax).foreach { k =>
      // assume all constraints hold in this step
      constraints.foreach(c => solver.assert(enc.getConstraint(c)))

      // make sure the constraints are not contradictory
      if(options.checkConstraints) {
        val res = solver.check(produceModel = false)
        assert(res.isSat, s"Found unsatisfiable constraints in cycle $k")
      }

      if(options.checkBadStatesIndividually) {
        // check each bad state individually
        bads.zipWithIndex.foreach { case (b, bi) =>
          solver.push()
          solver.assert(enc.getBadState(b))
          val res = solver.check(produceModel = false)

          // did we find an assignment for which the bad state is true?
          if(res.isSat) {
            val w = getWitness(sys, enc, k, Seq(bi))
            solver.pop()
            return ModelCheckFail(w)
          }
          solver.pop()
        }
      } else {
        val anyBad = smt.BVOr(bads.map(enc.getBadState))
        solver.push()
        solver.assert(anyBad)
        val res = solver.check(produceModel = false)

        // did we find an assignment for which at least one bad state is true?
        if(res.isSat) {
          val w = getWitness(sys, enc, k, bads.indices.toSeq)
          solver.pop()
          return ModelCheckFail(w)
        }
        solver.pop()
      }

      // advance
      enc.unroll(solver)
    }

    // clean up
    solver.pop()
    ModelCheckSuccess()
  }

  private def getWitness(sys: TransitionSystem, enc: SMTEncoding, kMax: Int, failedBad: Seq[Int]): Witness = {
    val regInit = sys.states.zipWithIndex.map { case (state, i) =>
      assert(!state.sym.isInstanceOf[smt.ArraySymbol], "TODO: support arrays!")
      val value = solver.getValue(enc.getSignalAt(state.sym.asInstanceOf[smt.BVSymbol], 0)).get
      i -> value
    }.toMap

    val inputs = (0 to kMax).map { k =>
      sys.inputs.zipWithIndex.map { case (input, i) =>
        val value = solver.getValue(enc.getSignalAt(input, k)).get
        i -> value
      }.toMap
    }

    Witness(failedBad, regInit, Map(), inputs)
  }

}

trait SMTEncoding {
  /** generate the system description */
  def defineHeader(solver: smt.Solver): Unit
  /** define the init state */
  def init(solver: smt.Solver): Unit
  /** add one more state */
  def unroll(solver: smt.Solver): Unit
  /** returns an expression representing the constraint in the current state */
  def getConstraint(name: String): smt.BVExpr
  /** returns an expression representing the constraint in the current state */
  def getBadState(name: String): smt.BVExpr
  /** returns an expression representing the signal in state k */
  def getSignalAt(sym: smt.BVSymbol, k: Int): smt.BVExpr
}