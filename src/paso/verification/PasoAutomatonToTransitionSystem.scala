// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import Chisel.log2Ceil
import maltese.mc.{IsBad, IsConstraint, Signal, SignalLabel, State, TransitionSystem}
import maltese.{mc, smt}
import paso.protocols._
import paso.untimed.MethodInfo
import scala.collection.mutable

/** Turns the PasoAutomaton into a TransitionSystem which can then be combined with the Design Under Verification
 *  for bounded model checking or inductive proofs.
 *
 *  - inputs: the paso automaton directly refers to the following signals:
 *    - inputs/outputs of the implementation
 *    - global reset and notReset signals
 *  - outputs:
 *    - startState: indicates that the automaton is in a state where a new transaction is started
 *    - initState: used to constrain the automaton to start in its initial state
 */
class PasoAutomatonToTransitionSystem(auto: PasoAutomaton) {
  import PredicateEncoder._

  private val signalPrefix = auto.untimed.name + ".automaton."
  private val stateBits = log2Ceil(auto.states.length + 1)
  private val inState = auto.states.map(s => smt.BVSymbol(signalPrefix + s"stateIs${s.id}", 1)).toArray
  private val invalidState = smt.BVSymbol(signalPrefix + "stateIsInvalid", 1)

  // global signals
  private val reset = smt.BVSymbol("reset", 1)
  private val notReset = smt.BVSymbol("notReset", 1)


  def run(): TransitionSystem = {
    // copy untimed model method semantics if necessary
    val (untimedSys, untimedInputs) = UntimedModelCopy.run(auto.untimed, auto.protocolCopies)

    // connect untimed system inputs (reset, method enabled and method args)
    val connectedUntimedSys = mc.TransitionSystem.connect(untimedSys, Map(
      s"${untimedSys.name}.reset" -> reset,
    ) ++ connectMethodEnabled(auto.commits, untimedInputs.enabled) ++
      connectMethodArgs(auto.mappings, untimedInputs.args)
    )

    // add the previous method arg states to the untimed sys
    val finalUntimedSys = connectedUntimedSys.copy(states = connectedUntimedSys.states ++ prevMethodArgs(untimedInputs.args))

    // turn the whole Paso FSM + assumptions + assertions into a transition system
    val pasoAutomaton = makePasoAutomaton()

    // we need to do a topological sort on the combined systems since not all signals might be in the correct order
    val combined = mc.TransitionSystem.combine(finalUntimedSys.name, List(finalUntimedSys, pasoAutomaton))
    TopologicalSort.run(combined)
  }

  private def makePasoAutomaton(): mc.TransitionSystem = {
    // define inState signals
    val state = smt.BVSymbol(signalPrefix + "state", stateBits)
    val maxState = smt.BVLiteral(auto.states.length - 1, stateBits)
    val stateSignals = inState.zip(auto.states).map { case (sym, st) =>
      Signal(sym.name, smt.BVEqual(state, smt.BVLiteral(st.id, stateBits)))
    } ++ Seq(
      mc.Signal(invalidState.name, smt.BVComparison(smt.Compare.Greater, state, maxState, signed=false)),
      mc.Signal(invalidState.name+"Check", not(smt.BVImplies(notReset, not(invalidState))), mc.IsBad)
    )

    // turn transaction start signals into signals
    val startSignals = auto.transactionStartSignals.map{ case (name, e) => mc.Signal(name, e) }

    // since we assume that everytime a transactions _can_ be started, a transaction _will_ be started, we just need
    // to check which state we are in
    val startTransactionStates = auto.states.filter(_.isStart).map(_.id).map(inState)
    val startAnyTransaction = List(mc.Signal(signalPrefix + "startState", smt.BVOr(startTransactionStates), mc.IsOutput))

    // signal that can be used to constrain the state to be zero
    val stateIsZero = List(mc.Signal(signalPrefix + "initState", inState(0), mc.IsOutput))

    // encode assertions and assumptions
    val assertions = compactEncodePredicates(auto.assertions, notReset, signalPrefix + "bad", IsBad, invert=true)
    val assumptions = compactEncodePredicates(auto.assumptions, notReset, signalPrefix + "constraint", IsConstraint, invert=false)

    // encode paso FSM state transitions
    val stateState = encodeStateEdges(state, auto.edges, reset)

    val signals = stateSignals ++ startSignals ++ stateIsZero ++ assumptions ++ assertions ++ startAnyTransaction
    mc.TransitionSystem("PasoAutomaton", List(), List(stateState), signals.toList)
  }

  private def connectMethodEnabled(commits: Seq[PasoGuardedCommit], enabled: Iterable[smt.BVSymbol]): Iterable[(String, smt.BVExpr)] = {
    val methodToCommits = commits.groupBy(_.commit.name)
    enabled.map { enabled =>
      val commits = methodToCommits.getOrElse(enabled.name, List())
      val en = if(commits.isEmpty) smt.False() else sumOfProduct(commits.map(c => inState(c.stateId) +: c.guard))
      enabled.name -> en
    }
  }

  private def connectMethodArgs(mappings: Seq[PasoStateGuardedMapping], args: Iterable[smt.BVSymbol]): Iterable[(String, smt.BVExpr)] = {
    val argsToMappings = mappings.groupBy(_.map.arg)
    args.map { arg =>
      val prev = arg.rename(arg.name + "$prev")
      val value = argsToMappings.getOrElse(arg, List()).foldLeft[smt.BVExpr](prev){(other, m) =>
        smt.BVIte(simplifiedProduct(inState(m.stateId) +: m.map.guard), m.map.update, other)
      }
      arg.name -> value
    }
  }

  private def prevMethodArgs(args: Iterable[smt.BVSymbol]): Iterable[State] = {
   args.map { arg =>
      val prev = arg.rename(arg.name + "$prev")
      mc.State(prev, init=None, next=Some(arg))
    }
  }

  private def encodeStateEdges(state: smt.BVSymbol, edges: Iterable[PasoStateEdge], reset: smt.BVExpr): State = {
    // we want to compute the next state based on the current state and predicates
    val invalidState = smt.BVLiteral((BigInt(1) << stateBits) - 1, stateBits)
    val next = edges.groupBy(_.to).foldLeft[smt.BVExpr](invalidState) { case (other, (nextState, edges)) =>
      val guard = sumOfProduct(edges.map(e => inState(e.from) +: e.guard))
      smt.BVIte(guard, smt.BVLiteral(nextState, stateBits), other)
    }
    val withReset = smt.BVIte(reset, smt.BVLiteral(0, stateBits), next)
    mc.State(state, init = None, next = Some(withReset))
  }

  /** the idea here is to group predicates that just have different guards */
  def compactEncodePredicates(preds: Iterable[PasoStateGuarded], notReset: smt.BVExpr, prefix: String, lbl: SignalLabel, invert: Boolean): Iterable[Signal] = {
    val notTriviallyTrue = preds.filterNot(_.pred.pred == smt.True())
    val groups = notTriviallyTrue.groupBy(_.pred.pred.toString)
    groups.zipWithIndex.map { case ((_, ps), i) =>
      val guard =  sumOfProduct(ps.map(p => inState(p.stateId) +: p.pred.guard))
      val pred = ps.head.pred.pred
      val expr = smt.BVImplies(smt.BVAnd(notReset, guard), pred)
      mc.Signal(s"${prefix}_$i", if(invert) not(expr) else expr, lbl)
    }
  }
}

object PredicateEncoder {
  def not(e: smt.BVExpr): smt.BVExpr = e match {
    case smt.BVNot(inner) => inner
    case o => smt.BVNot(o)
  }

  /** automatically simplifies */
  def simplifiedProduct(e: Iterable[smt.BVExpr]): smt.BVExpr = {
    val simplified = filterProductTerms(e)
    if(simplified.isEmpty) smt.True() else smt.BVAnd(simplified)
  }
  private def filterProductTerms(e: Iterable[smt.BVExpr]): Iterable[smt.BVExpr] = {
    val nonTriviallyTrue = e.filterNot(_ == smt.True())
    val simplifiedTerms = nonTriviallyTrue.map(smt.SMTSimplifier.simplify).map(_.asInstanceOf[smt.BVExpr])
    val uniqueTerms = simplifiedTerms.groupBy(_.toString).map(_._2.head)
    uniqueTerms
  }
  def sumOfProduct(e: Iterable[Iterable[smt.BVExpr]]): smt.BVExpr = {
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

case class UntimedInputInfo(enabled: Iterable[smt.BVSymbol], args: Iterable[smt.BVSymbol])

/** In order to support multiple copies of a single protocol, we also need to duplicate the combinatorial
 *  parts of the untimed module transaction that belongs to it. However, we leave all state shared.
 *  State will never be updated by two copies of the same protocol in the same cycle since a protocol
 *  always commits before forking, thus only a single protocol can commit every cycle.
 */
object UntimedModelCopy {
  def run(untimedModel: UntimedModel, protocolCopies: Seq[(String, Int)]): (mc.TransitionSystem, UntimedInputInfo) = {
    val methods = untimedModel.methods.map(m => (untimedModel.name + "." + m.name) -> m).toMap

    // calculate method inputs
    val infos = protocolCopies.map { case (methodName, copyCount) =>
      val suffixes = List("") ++ (1 until copyCount).map(i => s"$$$i")
      val method = methods(methodName)
      UntimedInputInfo(
        suffixes.map(s => method.fullIoName + "_enabled" + s).map(n => smt.BVSymbol(n, 1)),
        suffixes.flatMap(s => method.args.map{ case (name, w) => smt.BVSymbol(name + s, w) })
      )
    }
    val info = UntimedInputInfo(infos.flatMap(_.enabled), infos.flatMap(_.args))

    // shortcut if there are no copies
    if(protocolCopies.forall(_._2 <= 1)) {
      return (untimedModel.sys, info)
    }

    // do the actual copying:
    val copyOutputs = protocolCopies.filter(_._2 > 1).flatMap { case (methodName, copyCount) =>
      val outputs = methods(methodName).ret.map(_._1) // we do not need to copy the guard because it depends on the state only
      (1 until copyCount).flatMap(i => outputs.map(o => (o, s"$$$i")))
    }
    val sysWithCopiedOutputs = duplicateOutputs(untimedModel.sys, copyOutputs)

    val existingInputs = sysWithCopiedOutputs.inputs.map(_.name).toSet
    val inputCopies = protocolCopies.filter(_._2 > 1).flatMap { case (methodName, copyCount) =>
      val method = methods(methodName)
      val inputs = method.args.map(a => smt.BVSymbol(a._1, a._2)) :+ (smt.BVSymbol(method.fullIoName + "_enabled", 1))
      (1 until copyCount).flatMap(i => inputs.map(sym => sym.rename(sym.name + s"$$$i")))
    }.filterNot(i => existingInputs.contains(i.name))
    val sysWithAllInputAndOutputCopies = sysWithCopiedOutputs.copy(inputs = sysWithCopiedOutputs.inputs ++ inputCopies)

    // TODO
    assert(sysWithAllInputAndOutputCopies.states.isEmpty, "TODO: deal with states")

    (sysWithAllInputAndOutputCopies, info)
  }

  private def duplicateOutputs(sys: mc.TransitionSystem, copies: Seq[(String, String)]): mc.TransitionSystem = {
    if(copies.isEmpty) return sys
    // lookup table for dependencies
    val state = sys.states.map(_.name).toSet
    val deps = sys.signals.map(s => s.name -> (findSymbols(s.e).map(_.name).toSet -- state)).toMap
    val nameToSymbol = (sys.inputs ++ sys.signals.map(_.sym)).map(s => s.name -> s).toMap

    // for each copy, find all signals that it depends on and copy them in the order that they appear in the original
    val inputsAndSignals = copies.map { case(signal, suffix) =>
      val signalsToCopy = transitiveDeps(signal, deps) + signal
      val subs = signalsToCopy.map(n => n -> nameToSymbol(n).rename(n + suffix)).toMap
      val inputs = sys.inputs.filter(i => signalsToCopy(i.name)).map(i => i.rename(i.name + suffix))
      val signals = sys.signals.filter(s => signalsToCopy(s.name)).map{s =>
        mc.Signal(s.name + suffix, replace(s.e, subs), s.lbl)
      }
      (inputs, signals)
    }

    val newInputs = inputsAndSignals.flatMap(_._1)
    val newSignals = inputsAndSignals.flatMap(_._2)

    sys.copy(inputs = sys.inputs ++ newInputs, signals = sys.signals ++ newSignals)
  }

  private def transitiveDeps(start: String, deps: Map[String, Set[String]]): Set[String] = {
    val seen = mutable.HashSet[String]()
    val todo = mutable.ArrayStack[String]()
    todo.push(start)
    while(todo.nonEmpty) {
      val dependsOn = deps.getOrElse(todo.pop(), Set())
      dependsOn.diff(seen).foreach{d => todo.push(d) ; seen.add(d) }
    }
    seen.toSet
  }

  private def findSymbols(e: smt.SMTExpr): List[smt.SMTSymbol] = e match {
    case s: smt.BVSymbol => List(s)
    case s: smt.ArraySymbol => List(s)
    case other => other.children.flatMap(findSymbols)
  }

  private def replace(e: smt.SMTExpr, subs: Map[String, smt.SMTExpr]): smt.SMTExpr = e match {
    case s : smt.SMTSymbol => subs.getOrElse(s.name, s)
    case other => other.mapExpr(replace(_, subs))
  }
}