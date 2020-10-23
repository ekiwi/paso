// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import Chisel.log2Ceil
import maltese.smt
import paso.protocols._
import paso.untimed.MethodInfo

/** Turns the PasoAutomaton into a TransitionSystem which can then be combined with the Design Under Verification
 *  for bounded model checking or inductive proofs.
 */
class PasoAutomatonToTransitionSystem(auto: PasoAutomaton) {
  private val signalPrefix = auto.untimed.name + ".automaton."
  private val stateBits = log2Ceil(auto.states.length + 1)
  private val inState = auto.states.map(s => smt.BVSymbol(signalPrefix + s"state_is_${s.id}", 1)).toArray
  private val invalidState = smt.BVSymbol(signalPrefix + "state_is_invalid", 1)

  def run(): smt.TransitionSystem = {
    // TODO: deal with multiple copies of the same protocol/transaction

    // connect inState signals
    val state = smt.BVSymbol(signalPrefix + "state", stateBits)
    val maxState = smt.BVLiteral(auto.states.length - 1, stateBits)
    val stateSignals = inState.zip(auto.states).map { case (sym, st) =>
      smt.Signal(sym.name, smt.BVEqual(state, smt.BVLiteral(st.id, stateBits)))
    } :+ smt.Signal(invalidState.name, smt.BVComparison(smt.Compare.Greater, state, maxState, signed=false))

    // turn transaction start signals into signals
    val startSignals = auto.transactionStartSignals.map{ case (name, e) => smt.Signal(name, e) }

    // connect method enabled inputs and arguments
    val methodInputs = connectMethodEnabled(auto.commits, auto.untimed.methods) ++
      connectMethodArgs(auto.mappings, auto.untimed.methods)

    // encode assertions and assumptions
    val assertions = compactEncodePredicates(auto.assertions, signalPrefix + "bad", smt.IsBad, invert=true)
    val assumptions = compactEncodePredicates(auto.assumptions, signalPrefix + "constraint", smt.IsConstraint, invert=false)

    // protocol states are the previous argument trackers and the FSM state
    val states = Seq(encodeStateEdges(state, auto.edges)) ++ prevMethodArgs(auto.untimed.methods)

    // combine untimed model and paso automaton into a single transition system
    val allSignals = stateSignals ++ startSignals ++ methodInputs ++ auto.untimed.sys.signals ++ assumptions ++ assertions
    val allStates = states ++ auto.untimed.sys.states
    // we filter out all methods inputs
    val isMethodInput = methodInputs.map(_.name).toSet
    val combinedInputs = auto.untimed.sys.inputs.filterNot(i => isMethodInput(i.name))
    val combined = smt.TransitionSystem(auto.untimed.sys.name, combinedInputs, allStates.toList, allSignals.toList)

    // we need to do a topological sort on the combined systems since not all signals might be in the correct order
    TopologicalSort.run(combined)
  }

  private def connectMethodEnabled(commits: Seq[PasoGuardedCommit], methods: Iterable[MethodInfo]): Iterable[smt.Signal] = {
    val methodToCommits = commits.groupBy(_.commit.name)
    methods.map { m =>
      val signalName = m.fullIoName + "_enabled"
      val commits = methodToCommits.getOrElse(signalName, List())
      val en = if(commits.isEmpty) smt.False() else sumOfProduct(commits.map(c => inState(c.stateId) +: c.guard))
      smt.Signal(signalName, en)
    }
  }

  private def connectMethodArgs(mappings: Seq[PasoStateGuardedMapping], methods: Iterable[MethodInfo]): Iterable[smt.Signal] = {
    val argsToMappings = mappings.groupBy(_.map.arg)
    methods.flatMap { m => m.args.map { case (a, width) =>
      val arg = smt.BVSymbol(m.parent + "." + a, width)
      val prev = arg.rename(arg.name + "$prev")
      val value = argsToMappings.getOrElse(arg, List()).foldLeft[smt.BVExpr](prev){(other, m) =>
        smt.BVIte(simplifiedProduct(inState(m.stateId) +: m.map.guard), m.map.update, other)
      }
      smt.Signal(arg.name, value)
    }}
  }

  private def prevMethodArgs(methods: Iterable[MethodInfo]): Iterable[smt.State] = {
    methods.flatMap { m => m.args.map { case (a, width) =>
      val arg = smt.BVSymbol(m.parent + "." + a, width)
      val prev = arg.rename(arg.name + "$prev")
      smt.State(prev, init=None, next=Some(arg))
    }}
  }

  private def encodeStateEdges(state: smt.BVSymbol, edges: Iterable[PasoStateEdge]): smt.State = {
    // we want to compute the next state based on the current state and predicates
    val invalidState = smt.BVLiteral((BigInt(1) << stateBits) - 1, stateBits)
    val next = edges.groupBy(_.to).foldLeft[smt.BVExpr](invalidState) { case (other, (nextState, edges)) =>
      val guard = sumOfProduct(edges.map(e => inState(e.from) +: e.guard))
      smt.BVIte(guard, smt.BVLiteral(nextState, stateBits), other)
    }
    smt.State(state, init = Some(smt.BVLiteral(0, stateBits)), next = Some(next))
  }

  /** the idea here is to group predicates that just have different guards */
  private def compactEncodePredicates(preds: Iterable[PasoStateGuarded], prefix: String, lbl: smt.SignalLabel, invert: Boolean): Iterable[smt.Signal] = {
    val notTriviallyTrue = preds.filterNot(_.pred.pred == smt.True())
    val groups = notTriviallyTrue.groupBy(_.pred.pred.toString)
    groups.zipWithIndex.map { case ((_, ps), i) =>
      val guard =  sumOfProduct(ps.map(p => inState(p.stateId) +: p.pred.guard))
      val pred = ps.head.pred.pred
      val expr = smt.BVImplies(guard, pred)
      smt.Signal(s"${prefix}_$i", if(invert) not(expr) else expr, lbl)
    }
  }

  private def not(e: smt.BVExpr): smt.BVExpr = e match {
    case smt.BVNot(inner) => inner
    case o => smt.BVNot(o)
  }

  /** automatically simplifies */
  private def simplifiedProduct(e: Iterable[smt.BVExpr]): smt.BVExpr = {
    val simplified = filterProductTerms(e)
    if(simplified.isEmpty) smt.True() else smt.BVAnd(simplified)
  }
  private def filterProductTerms(e: Iterable[smt.BVExpr]): Iterable[smt.BVExpr] = {
    val nonTriviallyTrue = e.filterNot(_ == smt.True())
    val simplifiedTerms = nonTriviallyTrue.map(smt.SMTSimplifier.simplify).map(_.asInstanceOf[smt.BVExpr])
    val uniqueTerms = simplifiedTerms.groupBy(_.toString).map(_._2.head)
    uniqueTerms
  }
  private def sumOfProduct(e: Iterable[Iterable[smt.BVExpr]]): smt.BVExpr = {
    val products = e.map(filterProductTerms).filterNot(_.isEmpty).toArray

    // if terms are used more than once across products, we use distributivity to simplify
    val usageCounts = countTerms(products)
    val extractList = usageCounts.last._2
    if(extractList.size > 1) {
      val extractTerms = usageCounts.filter(_._2 == extractList).map(_._1)
      val otherProducts = (products.indices.toSet -- extractList.toSet).map(products)
      val remainingProducts = extractList.map(products).map(p => p.filterNot(extractTerms.contains(_)))

      val subProduct = extractTerms :+ sumOfProduct(remainingProducts)
      sumOfProduct(List(subProduct) ++ otherProducts)
    } else {
      smt.BVOr(products.map(smt.BVAnd(_)))
    }
  }
  private def countTerms(e: Iterable[Iterable[smt.BVExpr]]): Seq[(smt.BVExpr, List[Int])] = {
    val m = e.zipWithIndex.foldLeft(Map[smt.BVExpr, List[Int]]()){ case (map, (terms, i)) =>
      map ++ terms.map { t =>
        t -> (i +: map.getOrElse(t, List()))
      }
    }
    m.toSeq.sortBy(_._2.length)
  }
}
