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


  def run(invert: Boolean): TransitionSystem = {
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
    val pasoAutomaton = makePasoAutomaton(invert)

    // we need to do a topological sort on the combined systems since not all signals might be in the correct order
    val combined = mc.TransitionSystem.combine(finalUntimedSys.name, List(finalUntimedSys, pasoAutomaton))
    TopologicalSort.run(combined)
  }

  private def makePasoAutomaton(invert: Boolean): mc.TransitionSystem = {
    // define inState signals
    val state = smt.BVSymbol(signalPrefix + "state", stateBits)
    val maxState = smt.BVLiteral(auto.states.length - 1, stateBits)
    val stateSignals = inState.zip(auto.states).map { case (sym, st) =>
      Signal(sym.name, smt.BVEqual(state, smt.BVLiteral(st.id, stateBits)))
    } ++ Seq(
      mc.Signal(invalidState.name, smt.BVComparison(smt.Compare.Greater, state, maxState, signed=false)),
      mc.Signal(invalidState.name+"Check", not(smt.BVImplies(notReset, not(invalidState))), mc.IsBad)
    )

    // the active signal shows whether the particular transaction could be started
    val activeSignals = auto.transactionActiveSignals.map{ case (name, e) => mc.Signal(name, e) }

    // since we assume that everytime a transactions _can_ be started, a transaction _will_ be started, we just need
    // to check which state we are in
    val startTransactionStates = auto.states.filter(_.isStart).map(_.id).map(inState)
    val startAnyTransaction = List(mc.Signal(signalPrefix + "startState", smt.BVOr(startTransactionStates), mc.IsOutput))

    // signal that can be used to constrain the state to be zero
    val stateIsZero = List(mc.Signal(signalPrefix + "initState", inState(0), mc.IsOutput))

    // encode assertions and assumptions
    val assertions = compactEncodePredicates(auto.assertions, notReset, signalPrefix + "bad", assumeDontAssert = invert)
    val assumptions = compactEncodePredicates(auto.assumptions, notReset, signalPrefix + "constraint", assumeDontAssert = !invert)

    // encode paso FSM state transitions
    val stateState = encodeStateEdges(state, auto.edges, reset)

    val signals = stateSignals ++ activeSignals ++ stateIsZero ++ assumptions ++ assertions ++ startAnyTransaction
    mc.TransitionSystem("PasoAutomaton", List(), List(stateState), signals.toList)
  }

  private def connectMethodEnabled(commits: Seq[PasoGuardedSignal], enabled: Iterable[smt.BVSymbol]): Iterable[(String, smt.BVExpr)] = {
    val methodToCommits = commits.groupBy(_.signal.name)
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
  def compactEncodePredicates(preds: Iterable[PasoStateGuarded], notReset: smt.BVExpr, prefix: String, assumeDontAssert: Boolean): Iterable[Signal] = {
    val negate = !assumeDontAssert
    val lbl = if(assumeDontAssert) mc.IsConstraint else mc.IsBad
    val notTriviallyTrue = preds.filterNot(_.pred.pred == smt.True())
    val groups = notTriviallyTrue.groupBy(_.pred.pred.toString)
    groups.zipWithIndex.map { case ((_, ps), i) =>
      val guard =  sumOfProduct(ps.map(p => inState(p.stateId) +: p.pred.guard))
      val pred = ps.head.pred.pred
      val expr = smt.BVImplies(smt.BVAnd(notReset, guard), pred)
      mc.Signal(s"${prefix}_$i", if(negate) not(expr) else expr, lbl)
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

case class UntimedInputInfo(enabled: Iterable[smt.BVSymbol], start: Iterable[smt.BVSymbol], args: Iterable[smt.BVSymbol])

/** In order to support multiple copies of a single protocol, we also need to duplicate the combinatorial
 *  parts of the untimed module transaction that belongs to it. However, we leave all state shared.
 *  State will never be updated by two copies of the same protocol in the same cycle since a protocol
 *  always commits before forking, thus only a single protocol can commit every cycle.
 */
object UntimedModelCopy {
  def run(untimedModel: UntimedModel, protocolCopies: Seq[(String, Int)]): (mc.TransitionSystem, UntimedInputInfo) = {
    val methods = untimedModel.methods.map(m => (untimedModel.name + "." + m.name) -> m).toMap

    // Duplicate states (as far as necessary):
    // For protocols with multiple copies we need to keep a separate copy of the untimed module state
    // in order to be able to compute the result over the old state even when the protocol has already committed
    val sysWithCopiedStates = duplicateStates(untimedModel.sys, methods, protocolCopies)

    // copy outputs (as far as necessary)
    val copyOutputs = protocolCopies.filter(_._2 > 1).flatMap { case (methodName, copyCount) =>
      val method = methods(methodName)
      // we do not need to copy the guard because it depends on the state only
      val outputs = method.ret.map(_._1)
      (0 until copyCount).flatMap(i => outputs.map(o => (o, method.name, s"$$$i")))
    }
    val sysWithCopiedOutputs = duplicateOutputs(sysWithCopiedStates, copyOutputs)



    // if there is only a single copy, we just need to rename the output (by creating a copy)
    val outputsAliases = protocolCopies.filter(_._2 == 1).flatMap { case (methodName, copyCount) =>
      methods(methodName).ret.map { case (name, w) =>
        mc.Signal(name + "$0", smt.BVSymbol(name, w), mc.IsOutput)
      }
    }

    // connect method inputs
    val (sysWithInputsConnected, info) = connectInputs(sysWithCopiedOutputs, protocolCopies, methods)

    val finalSys = sysWithInputsConnected.copy(
      inputs = sysWithInputsConnected.inputs ++ info.enabled ++ info.start ++ info.args,
      signals = sysWithInputsConnected.signals ++ outputsAliases,
    )

    println(untimedModel.sys.serialize)
    println()
    println(finalSys.serialize)

    (finalSys, info)
  }

  private def connectInputs(sys: mc.TransitionSystem, protocolCopies: Seq[(String, Int)], methods: Map[String, MethodInfo]):
  (mc.TransitionSystem, UntimedInputInfo) = {
    val enabledInputs = mutable.ArrayBuffer[smt.BVSymbol]()
    val startInputs = mutable.ArrayBuffer[smt.BVSymbol]()
    val argInputs = mutable.ArrayBuffer[smt.BVSymbol]()
    val inputConnections = protocolCopies.flatMap { case (methodName, copyCount) =>
      val suffixes = (0 until copyCount).map(i => s"$$$i")
      val method = methods(methodName)
      val enabled = suffixes.map(s => smt.BVSymbol(method.fullIoName + "_enabled" + s, 1))
      enabledInputs ++= enabled
      if(suffixes.length > 1) {
        startInputs ++= suffixes.map(s => smt.BVSymbol(method.fullIoName + "_start" + s, 1))
      }
      // Only one enabled signal (per method) will be true in any cycle (one hot encoded!)
      // If any of them is true, we want to commit the state.
      val conEnabled = List((method.fullIoName + "_enabled") -> smt.BVOr(enabled))
      // We need to connect the args associated with the active enabled signal
      val conArgs = method.args.map { case (name, w) =>
        val argCopies = suffixes.map(s => smt.BVSymbol(name + s, w))
        argInputs ++= argCopies
        // pick the copy associated with the enabled copy
        name -> argCopies.zip(enabled).drop(1)
          .foldLeft[smt.BVExpr](argCopies.head){ case (other, (arg, enabled)) => smt.BVIte(enabled, arg, other) }
      }
      conEnabled ++ conArgs
    }.toMap
    val info = UntimedInputInfo(enabledInputs, startInputs, argInputs)
    (mc.TransitionSystem.connect(sys, inputConnections), info)
  }

  private def duplicateOutputs(sys: mc.TransitionSystem, copies: Seq[(String, String, String)]): mc.TransitionSystem = {
    if(copies.isEmpty) return sys
    // lookup table for dependencies
    val isIO = (sys.inputs.map(_.name) ++ sys.signals.filter(_.lbl == mc.IsOutput).map(_.name)).toSet
    val deps = sys.signals.map(s => s.name -> (findSymbols(s.e).map(_.name).toSet)).toMap
    val nameToSymbol = (sys.inputs ++ sys.signals.map(_.sym) ++ sys.states.map(_.sym)).map(s => s.name -> s).toMap

    // We rename inputs and outputs only by their suffix since they are exclusive to their respective methods
    // Internal signals and states however could be shared, thus they also need the method name.
    def rename(name: String, method: String, suffix: String): String =
      if(isIO(name)) { name + suffix } else { s"$name$$$method$suffix" }

    // for each copy, find all signals that it depends on and copy them in the order that they appear in the original
    // most inputs do not need to be copies since they are automatically duplicated with the protocol
    val alreadyCopied = mutable.HashSet[String]()
    val inputsAndSignals = copies.map { case(signal, method, suffix) =>
      val signalsToCopy = transitiveDeps(signal, deps) + signal
      val subs = signalsToCopy.map(n => n -> nameToSymbol(n).rename(rename(n, method, suffix))).toMap
      val signals = sys.signals.filter(s => signalsToCopy(s.name) && !alreadyCopied(rename(s.name, method, suffix))).map { s =>
        mc.Signal(rename(s.name, method, suffix), replace(s.e, subs), s.lbl)
      }
      // we need to possible duplicate any random inputs
      val inputs = sys.inputs.filter(_.name.contains("RANDOM"))
        .filter(i => signalsToCopy(i.name) && !alreadyCopied(i.name + suffix))
        .map(i => i.rename(i.name + suffix))
      // remember which copied signals we have already created
      alreadyCopied ++= inputs.map(_.name) ++ signals.map(_.name)
      (inputs, signals)
    }

    val newInputs = inputsAndSignals.flatMap(_._1)
    val newSignals = inputsAndSignals.flatMap(_._2)

    sys.copy(inputs = sys.inputs ++ newInputs, signals = sys.signals ++ newSignals)
  }

  private def duplicateStates(sys: TransitionSystem, methods: Map[String, MethodInfo], protocolCopies: Seq[(String, Int)]): TransitionSystem = {
    // For protocols with multiple copies we need to keep a separate copy of the untimed module state
    // in order to be able to compute the result over the old state even when the protocol has already committed
    val stateAndSignals = protocolCopies.filter(_._2 > 1).flatMap { case (methodName, copyCount) =>
      val method = methods(methodName)
      (0 until copyCount).flatMap { i => sys.states.map { state =>
        val stateCopy = state.sym.rename(state.name + s"$$${method.name}$$$i")
        // keep the last value of stateCopy around
        val prev = mc.State(stateCopy.rename(stateCopy.name + "_prev"), None, Some(stateCopy))
        // the copied state is the same as before unless the transaction is started in this cycle
        val start = smt.BVSymbol(method.fullIoName + s"_start$$$i", 1)
        val signal = mc.Signal(stateCopy.name, smt.SMTIte(start, state.sym, prev.sym))
        (prev, signal)
      }}
    }
    sys.copy(states = sys.states ++ stateAndSignals.map(_._1), signals = sys.signals ++ stateAndSignals.map(_._2))
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