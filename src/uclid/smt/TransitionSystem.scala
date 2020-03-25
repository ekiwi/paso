/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2020. The Regents of the University of California
 *
 * All Rights Reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from this
 * software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Author: Kevin Laeufer <laeufer@cs.berkeley.edu>
 *
 */

package uclid.smt

case class State(sym: Symbol, init: Option[Expr] = None, next: Option[Expr]= None)
case class TransitionSystem(name: Option[String], inputs: Seq[Symbol], states: Seq[State],
                            outputs: Seq[Tuple2[String,Expr]] = Seq(),
                            constraints: Seq[Expr] = Seq(), bad: Seq[Expr] = Seq(), fair: Seq[Expr] = Seq()) {
  private def disjunction(props: Seq[Expr]): Seq[Expr] = if(props.isEmpty) {Seq()} else {
    Seq(props.reduce{ (a,b) => OperatorApplication(DisjunctionOp, List(a, b)) })
  }
  // ensures that the number of bad states is 1 or 0
  def unifyProperties(): TransitionSystem = {
    this.copy(bad = disjunction(this.bad))
  }
  /* ensures that states are ordered by the dependencies in their init expressions */
  def sortStatesByInitDependencies(): TransitionSystem = {
    val stateSymbols = states.map(_.sym).toSet
    val dependencies = states.map { st =>
      st.sym -> st.init.toSeq.flatMap(Context.findSymbols).toSet.intersect(stateSymbols).diff(Set(st.sym))
    }.toMap
    val dependencyGraph = firrtl.graph.DiGraph(dependencies).reverse
    val stateOrder = dependencyGraph.linearize
    val stateSymToState = states.map{st => st.sym -> st}.toMap
    this.copy(states = stateOrder.map(stateSymToState))
  }
}

trait ModelCheckResult {
  def isFail: Boolean
  def isSuccess: Boolean = !isFail
}
case class ModelCheckSuccess() extends ModelCheckResult { override def isFail: Boolean = false }
case class ModelCheckFail(witness: Witness) extends ModelCheckResult { override def isFail: Boolean = true }

case class Witness(failedBad: Seq[Int], regInit: Map[Int, BigInt], memInit: Map[Int, Seq[(BigInt, BigInt)]], inputs: Seq[Map[Int, BigInt]])

class TransitionSystemSimulator(sys: TransitionSystem) {
  val inputs: Map[Int, Symbol] = sys.inputs.zipWithIndex.map{ case (input, index) => index -> input }.toMap
  val states: Map[Int, State] = sys.states.zipWithIndex.map{ case (state, index) => index -> state}.toMap


}


object BitVectorSemantics {
  def binary(op: Operator, a: BigInt, b: BigInt): BigInt = op match {
    case BVAddOp(w) => a + b
  }
}