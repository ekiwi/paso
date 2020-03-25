package paso.verification

import uclid.smt

/** turns all identifiers used in a verification problem into their fully qualified names */
object NamespaceIdentifiers {
  type Sub = Map[smt.Expr, smt.Expr]
  type SymSub =  Map [smt.Expr, smt.Symbol]

  def apply(p: VerificationProblem): VerificationProblem = {
    val (untimed, u_subs, m_subs) = apply(p.untimed, "")
    val (impl, i_subs) = apply(p.impl, "")
    val subs = u_subs ++ i_subs
    val protocols = p.protocols.map{ case(name, graph) => (untimed.name + "." + name, apply(graph, subs, m_subs)) }
    VerificationProblem(
      impl=impl, untimed=untimed, protocols=protocols,
      invariances = p.invariances.map(apply(_, subs)),
      mapping = p.mapping.map(apply(_, subs))
    )
  }

  def apply(a: Assertion, subs: Sub): Assertion = Assertion(substituteSmt(a.guard, subs), substituteSmt(a.pred, subs))

  def apply(node: PendingInputNode, subs: Sub, sm: Map[String, String]): PendingInputNode = PendingInputNode(node.next.map(apply(_, subs, sm)))
  def apply(node: PendingOutputNode, subs: Sub, sm: Map[String, String]): PendingOutputNode = PendingOutputNode(node.next.map(apply(_, subs, sm)))
  def apply(edge: InputEdge, subs: Sub, sm: Map[String, String]): InputEdge =
    InputEdge(edge.constraints.map(substituteSmt(_, subs)), edge.mappings.map(substituteSmt(_, subs)),
      edge.methods.map(sm), apply(edge.next, subs, sm))
  def apply(edge: OutputEdge, subs: Sub, sm: Map[String, String]): OutputEdge =
    OutputEdge(edge.constraints.map(substituteSmt(_, subs)), edge.mappings.map(substituteSmt(_, subs)),
      edge.methods.map(sm), apply(edge.next, subs, sm))


  def apply(untimed: UntimedModel, prefix: String): (UntimedModel, Sub, Map[String, String]) = {
    val fullPrefix = prefix + untimed.name + "."
    val args = untimed.methods.flatMap{case (name, sem) =>
      sem.inputs.map{ i => i.copy(id = name + "." + i.id) } ++
      sem.outputs.map{ case NamedExpr(sym, _) => sym.copy(id = name + "." + sym.id) }
    }
    val internal_args = untimed.methods.flatMap{case (name, sem) =>
      (sem.inputs ++ sem.outputs.map(_.sym)).prefix(fullPrefix + name + ".")
    }
    val isubs : SymSub = (untimed.state.prefix(fullPrefix) ++ internal_args).toMap
    def rename(name: String, s: MethodSemantics): MethodSemantics =
      MethodSemantics(substituteSmt(s.guard, isubs), s.updates.map(renameNamed), s.outputs.map(renameNamed), s.inputs.map(isubs))
    def renameNamed(n: NamedExpr): NamedExpr = NamedExpr(isubs(n.sym), expr = substituteSmt(n.expr, isubs))
    val renamed_untimed = UntimedModel(
      name = fullPrefix.dropRight(1),
      state = untimed.state.map(isubs),
      methods = untimed.methods.map{ case (name, s) => (fullPrefix + name,  rename(name, s))},
      init = untimed.init.map(renameNamed)
    )
    val subs : SymSub = (untimed.state ++ args).prefix(fullPrefix).toMap
    val method_subs = untimed.methods.map{case (name, _) => name -> (fullPrefix + name)}
    (renamed_untimed, subs, method_subs)
  }

  def apply(sys: smt.TransitionSystem, prefix: String): (smt.TransitionSystem, Sub)= {
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
  def apply[E <: smt.Expr](a: Assertion, map: Map[smt.Expr, E]): Assertion =
    Assertion(guard = apply(a.guard, map), pred = apply(a.pred, map))
}