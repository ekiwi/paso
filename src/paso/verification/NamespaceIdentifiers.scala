package paso.verification

import uclid.smt

/**
 * turns all identifiers used in a verification problem into their fully qualified names
 *
 * For Untimed Modules:
 * - for the main spec, prefix="", for the subspecs, prefix = "${instanceName}."
 * - we prefix the name with ${prefix}
 * - we prefix the state with ${prefix}${moduleName}.
 * - we prefix method arguments (+ ret arguments) with ${prefix}${moduleName}.${methodName}.
 * - the renamed state needs to be propagated to invariances/mappings which refer to it
 * - the renamed method arguments need to be propagated to protocols which refer to them
 *
 * For Transition Systems (implementation):
 * - we prefix all signals (states, inputs, outputs) with ${systemName}.
 * - this information needs to be propagated to protocols which refer to I/O and
 *   invariances/mappings which refer to state
 * */
object NamespaceIdentifiers {
  type SymSub =  Map [smt.Expr, smt.Symbol]

  def apply(p: VerificationProblem): VerificationProblem = {
    val (impl, ioSubs, _) = renameSys(p.impl)
    val (spec, _) = renameSpec("", p.spec, ioSubs)
    val subspecs = p.subspecs.map(renameSubspec(_, ioSubs))

    val invariantPrefixSubs = List(
      impl.name.get -> s"${impl.name.get}.signals", spec.untimed.name -> s"${spec.untimed.name}.signals"
    )
    val invariances = p.invariances.map(renameAssert(_, invariantPrefixSubs))
    val mapping = p.mapping.map(renameAssert(_, invariantPrefixSubs))

    VerificationProblem(impl, spec, subspecs, invariances, mapping)
  }

  // substitutes things like:
  // RandomLatency_running -> RandomLatency.signals_running
  def renameAssert(a: Assertion, prefixSubs: List[(String, String)]): Assertion = a match {
    case BasicAssertion(guard, pred) =>
      BasicAssertion(substitutePrefix(guard, prefixSubs), substitutePrefix(pred, prefixSubs))
    case ForAllAssertion(variable, start, end, guard, pred) =>
      ForAllAssertion(variable, start, end, substitutePrefix(guard, prefixSubs), substitutePrefix(pred, prefixSubs))
  }

  // used for both, the implementation and the untimed specification transition system
  def renameSys(sys: smt.TransitionSystem): (smt.TransitionSystem, SymSub, SymSub) = {
    // we want to prefix state and io with the name of the toplevel module
    val prefix = sys.name.get + "."
    val outputSymbols = sys.outputs.map{ case (name, expr) => smt.Symbol(name, expr.typ) }
    val ioSubs : SymSub = (sys.inputs ++ outputSymbols).prefix(prefix).toMap
    val stateSubs : SymSub = sys.states.map(_.sym).prefix(prefix).toMap

    val subs = ioSubs ++ stateSubs
    def rename(s: smt.State): smt.State =
      smt.State(subs(s.sym), s.init.map(substituteSmt(_, subs)), s.next.map(substituteSmt(_, subs)))
    val renamed_sys = smt.TransitionSystem(
      name = sys.name,
      inputs = sys.inputs.map(subs),
      states = sys.states.map(rename),
      outputs = sys.outputs.map{ case (name, expr) => (prefix + name, substituteSmt(expr, subs)) },
      constraints = sys.constraints.map(substituteSmt(_, subs)),
      bad = sys.bad.map(substituteSmt(_, subs)),
      fair = sys.fair.map(substituteSmt(_, subs)),
    )

    (renamed_sys, ioSubs, stateSubs)
  }

  def renameSubspec(s: Subspec, ioSubs: SymSub): Subspec = {
    val p = s.instance + "."
    val localIoSubs : SymSub = s.ioSymbols.map(s => s -> ioSubs(s.copy(id = p + s.id))).toMap
    val spec = renameSpec(s.instance + ".", s.spec, localIoSubs)._1
    s.copy(spec = spec)
  }

  def renameSpec(prefix: String, spec: Spec, implIoSubs: SymSub): (Spec, SymSub) = {
    val (renamedSys, ioSubs, stateSubs) = renameSys(spec.untimed.sys.copy(name = Some(prefix + spec.untimed.name)))
    val renamedMethods = spec.untimed.methods.map(m => m.copy(ioName = renamedSys.name + "." + m.ioName))
    val renamedUntimed = UntimedModel(renamedSys, renamedMethods)

    /*
    val args = spec.untimed.methods.flatMap{case (name, sem) =>
      sem.inputs.map{ i => i.copy(id = name + "." + i.id) } ++
        sem.outputs.flatMap{ case NamedGuardedExpr(sym, _,_) => Seq(sym.copy(id = name + "." + sym.id) ,
          smt.Symbol(name + "." + sym.id + ".valid", smt.BoolType))}
    }
    val specIoSubs : SymSub = args.prefix(fullPrefix).toMap
    val methodNameSubs = spec.untimed.methods.map{case (name, _) => name -> name} // TODO: should this be prefixed or not?
    val protocolIoSubs = specIoSubs ++ implIoSubs
    val renamedProtocols = spec.protocols.map{ case(name, graph) => (name, renameProtocol(graph, protocolIoSubs, methodNameSubs)) }
     */
    // TODO: properly rename protocols
    val renamedProtocols = spec.protocols


    (Spec(renamedUntimed, renamedProtocols), stateSubs)
  }

  def renameProtocol(node: StepNode, subs: SymSub, sm: Map[String, String]): StepNode =
    StepNode(node.next.map(renameProtocol(_, subs, sm)), node.methods.map(sm), node.id, node.isFork)
  def renameProtocol(node: InputNode, subs: SymSub, sm: Map[String, String]): InputNode =
    InputNode(node.next.map(renameProtocol(_, subs, sm)), node.methods.map(sm),
      node.constraints.map(substituteSmt(_, subs)), node.mappings.map(apply(_, subs)))
  def renameProtocol(node: OutputNode, subs: SymSub, sm: Map[String, String]): OutputNode =
    OutputNode(node.next.map(renameProtocol(_, subs, sm)), node.methods.map(sm),
      node.constraints.map(substituteSmt(_, subs)), node.mappings.map(apply(_, subs)))

  def apply(e: ArgumentEq, subs: SymSub): ArgumentEq =
    e.copy(range = apply(e.range, subs), argRange = apply(e.argRange, subs))
  def apply(r: Range, subs: SymSub): Range =
    if(subs.contains(r.sym)) r.copy(sym = subs(r.sym)) else r

  // helper functions
  implicit class symbolSeq(x: Iterable[smt.Symbol]) {
    def prefix(p: String): Iterable[(smt.Symbol, smt.Symbol)] = x.map(s => s -> smt.Symbol(p + s.id, s.typ))
    def suffix(suf: String): Iterable[(smt.Symbol, smt.Symbol)] = x.map(s => s -> smt.Symbol(s.id + suf, s.typ))
  }
}

object substituteSmt {
  def apply[E <: smt.Expr](expr: smt.Expr, map: Map[smt.Expr, E]): smt.Expr = map.getOrElse(expr, { expr match {
    case e : smt.Symbol => e
    case e : smt.OperatorApplication => e.copy(operands = e.operands.map(apply(_, map)))
    case e : smt.Literal => e
    case s : smt.ArraySelectOperation => s.copy(e = apply(s.e, map), index = s.index.map(apply(_, map)))
    case s : smt.ArrayStoreOperation => s.copy(e = apply(s.e, map), index = s.index.map(apply(_, map)), value = apply(s.value, map))
    case s : smt.FunctionApplication => s.copy(args = s.args.map(apply(_, map)))
    case s : smt.ConstArray => s.copy(expr = apply(s.expr, map))
    case other => throw new NotImplementedError(s"TODO: deal with $other")
  }})
  def apply[E <: smt.Expr](a: Assertion, map: Map[smt.Expr, E]): Assertion = a match {
    case BasicAssertion(guard, pred) =>
      BasicAssertion(substituteSmt(guard, map), substituteSmt(pred, map))
    case ForAllAssertion(variable, start, end, guard, pred) =>
      ForAllAssertion(variable, start, end, substituteSmt(guard, map), substituteSmt(pred, map))
  }
}

object substitutePrefix {
  def apply[E <: smt.Expr](expr: smt.Expr, subs: List[(String, String)]): smt.Expr = expr match {
    case e : smt.Symbol =>
      subs.find(s => e.id.startsWith(s._1))
        .map { case (o, n) => n + e.id.substring(o.length) }
        .map(i => e.copy(id = i))
        .getOrElse(e)
    case e : smt.OperatorApplication => e.copy(operands = e.operands.map(apply(_, subs)))
    case e : smt.Literal => e
    case s : smt.ArraySelectOperation => s.copy(e = apply(s.e, subs), index = s.index.map(apply(_, subs)))
    case s : smt.ArrayStoreOperation => s.copy(e = apply(s.e, subs), index = s.index.map(apply(_, subs)), value = apply(s.value, subs))
    case s : smt.FunctionApplication => s.copy(args = s.args.map(apply(_, subs)))
    case s : smt.ConstArray => s.copy(expr = apply(s.expr, subs))
    case other => throw new NotImplementedError(s"TODO: deal with $other")
  }
}