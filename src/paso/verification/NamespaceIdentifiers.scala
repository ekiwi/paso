package paso.verification

import uclid.smt

/** turns all identifiers used in a verification problem into their fully qualified names */
object NamespaceIdentifiers {
  type Sub = Map[smt.Expr, smt.Expr]
  type SymSub =  Map [smt.Expr, smt.Symbol]

  def apply(p: VerificationProblem): VerificationProblem = {
    val (untimed, u_subs, m_subs) = apply(p.spec.untimed, "")
    val (impl, i_subs) = apply(p.impl, "")
    val subs = u_subs ++ i_subs
    val protocols = p.spec.protocols.map{ case(name, graph) => (name, apply(graph, subs, m_subs)) }
    assert(p.subspecs.isEmpty, "TODO")
    VerificationProblem(
      impl=impl, spec=Spec(untimed=untimed, protocols=protocols),
      subspecs = Map(),
      invariances = p.invariances.map(substituteSmt(_, subs)),
      mapping = p.mapping.map(substituteSmt(_, subs))
    )
  }

  def apply(node: StepNode, subs: SymSub, sm: Map[String, String]): StepNode =
    StepNode(node.next.map(apply(_, subs, sm)), node.methods.map(sm))
  def apply(node: InputNode, subs: SymSub, sm: Map[String, String]): InputNode =
    InputNode(node.next.map(apply(_, subs, sm)), node.methods.map(sm),
      node.constraints.map(substituteSmt(_, subs)), node.mappings.map(apply(_, subs)))
  def apply(node: OutputNode, subs: SymSub, sm: Map[String, String]): OutputNode =
    OutputNode(node.next.map(apply(_, subs, sm)), node.methods.map(sm),
      node.constraints.map(substituteSmt(_, subs)), node.mappings.map(apply(_, subs)))

  def apply(e: ArgumentEq, subs: SymSub): ArgumentEq =
    e.copy(range = apply(e.range, subs), argRange = apply(e.argRange, subs))
  def apply(r: Range, subs: SymSub): Range =
    if(subs.contains(r.sym)) r.copy(sym = subs(r.sym)) else r

  def apply(untimed: UntimedModel, prefix: String): (UntimedModel, SymSub, Map[String, String]) = {
    val fullPrefix = prefix + untimed.name + "."

    val stateSubs: SymSub = untimed.state.map(_.sym).prefix(fullPrefix).toMap
    def rename(name: String, s: MethodSemantics): MethodSemantics = {
      val subs: SymSub = (s.inputs ++ s.outputs.map(_.sym)).prefix(fullPrefix + name + ".").toMap ++ stateSubs
      MethodSemantics(substituteSmt(s.guard, subs), s.updates.map(renameNamed(_, subs)), s.outputs.map(renameGuardedNamed(_, subs)), s.inputs.map(subs))
    }
    def renameNamed(n: NamedExpr, subs: SymSub): NamedExpr = {
      NamedExpr(subs(n.sym), expr = substituteSmt(n.expr, subs))
    }
    def renameGuardedNamed(n: NamedGuardedExpr, subs: SymSub): NamedGuardedExpr = {
      NamedGuardedExpr(subs(n.sym), expr = substituteSmt(n.expr, subs), guard = substituteSmt(n.guard, subs))
    }

    val renamed_untimed = UntimedModel(
      name = fullPrefix.dropRight(1),
      state = untimed.state.map(st => st.copy(sym = stateSubs(st.sym))), // we assume that all inits are constant
      methods = untimed.methods.map{ case (name, s) => (name,  rename(name, s))},
    )

    // substitutions for protocols
    val args = untimed.methods.flatMap{case (name, sem) =>
      sem.inputs.map{ i => i.copy(id = name + "." + i.id) } ++
        sem.outputs.flatMap{ case NamedGuardedExpr(sym, _,_) => Seq(sym.copy(id = name + "." + sym.id) ,
          smt.Symbol(name + "." + sym.id + ".valid", smt.BoolType))}
    }
    val subs : SymSub = (untimed.state.map(_.sym) ++ args).prefix(fullPrefix).toMap
    val method_subs = untimed.methods.map{case (name, _) => name -> name} // TODO: should this be prefixed or not?
    (renamed_untimed, subs, method_subs)
  }

  def apply(sys: smt.TransitionSystem, prefix: String): (smt.TransitionSystem, SymSub)= {
    val fullPrefix = prefix + sys.name.map(_ + ".").getOrElse("")
    val outputSymbols = sys.outputs.map{ case (name, expr) => smt.Symbol(name, expr.typ) }
    val subs : SymSub = (sys.states.map(_.sym) ++ sys.inputs ++ outputSymbols).prefix(fullPrefix).toMap
    def rename(s: smt.State): smt.State =
      smt.State(subs(s.sym), s.init.map(substituteSmt(_, subs)), s.next.map(substituteSmt(_, subs)))
    val renamed_sys = smt.TransitionSystem(
      name = Some(fullPrefix.dropRight(1)),
      inputs = sys.inputs.map(subs),
      states = sys.states.map(rename),
      outputs = sys.outputs.map{ case (name, expr) => (fullPrefix + name, substituteSmt(expr, subs)) },
      constraints = sys.constraints.map(substituteSmt(_, subs)),
      bad = sys.bad.map(substituteSmt(_, subs)),
      fair = sys.fair.map(substituteSmt(_, subs)),
    )
    (renamed_sys, subs)
  }

  // helper functions
  implicit class symbolSeq(x: Iterable[smt.Symbol]) {
    def prefix(p: String): Iterable[(smt.Symbol, smt.Symbol)] = x.map(s => s -> smt.Symbol(p + s.id, s.typ))
    def suffix(suf: String): Iterable[(smt.Symbol, smt.Symbol)] = x.map(s => s -> smt.Symbol(s.id + suf, s.typ))
  }
  //implicit def mapToSymbols(m: Iterable[(String, smt.Type)]): Iterable[smt.Symbol] = m.map{ case (name, tpe) => smt.Symbol(name, tpe)}
}

object substituteSmt {
  def apply[E <: smt.Expr](expr: smt.Expr, map: Map[smt.Expr, E]): smt.Expr = map.getOrElse(expr, { expr match {
    case e : smt.Symbol => e
    case e : smt.OperatorApplication => e.copy(operands = e.operands.map(apply(_, map)))
    case e : smt.Literal => e
    case s : smt.ArraySelectOperation => s.copy(e = apply(s.e, map), index = s.index.map(apply(_, map)))
    case s : smt.ArrayStoreOperation => s.copy(e = apply(s.e, map), index = s.index.map(apply(_, map)), value = apply(s.value, map))
    case other => throw new NotImplementedError(s"TODO: deal with $other")
  }})
  def apply[E <: smt.Expr](a: Assertion, map: Map[smt.Expr, E]): Assertion = a match {
    case BasicAssertion(guard, pred) =>
      BasicAssertion(substituteSmt(guard, map), substituteSmt(pred, map))
    case ForAllAssertion(variable, start, end, guard, pred) =>
      ForAllAssertion(variable, start, end, substituteSmt(guard, map), substituteSmt(pred, map))
  }
}