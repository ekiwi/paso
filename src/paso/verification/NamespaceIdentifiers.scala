package paso.verification

import uclid.smt

/** turns all identifiers used in a verification problem into their fully qualified names */
object NamespaceIdentifiers {
  def apply(p: VerificationProblem): VerificationProblem = {
    p
  }



  def apply(sys: smt.SymbolicTransitionSystem, prefix: String = ""): smt.SymbolicTransitionSystem = {
    val outputs = sys.outputs.map{ case (name, expr) => smt.Symbol(name, expr.typ) }
    val subs = (sys.states.map(_.sym) ++ sys.inputs ++ outputs).prefix(prefix).toMap

    sys
  }

  // helper functions
  implicit class symbolSeq(x: Iterable[smt.Symbol]) {
    def prefix(p: String): Iterable[(smt.Symbol, smt.Symbol)] = x.map(s => s -> smt.Symbol(p + s.id, s.typ))
    def suffix(suf: String): Iterable[(smt.Symbol, smt.Symbol)] = x.map(s => s -> smt.Symbol(s.id + suf, s.typ))
  }
  implicit def mapToSymbols(m: Iterable[(String, smt.Type)]): Iterable[smt.Symbol] = m.map{ case (name, tpe) => smt.Symbol(name, tpe)}
}

object substituteSmt {
  def apply(expr: smt.Expr, map: Map[smt.Expr, smt.Expr]): smt.Expr = map.getOrElse(expr, { expr match {
    case e : smt.Symbol => e
    case e : smt.OperatorApplication => e.copy(operands = e.operands.map(apply(_, map)))
    case e : smt.Literal => e
    case s : smt.ArraySelectOperation => s.copy(e = apply(s.e, map), index = s.index.map(apply(_, map)))
    case s : smt.ArrayStoreOperation => s.copy(e = apply(s.e, map), index = s.index.map(apply(_, map)), value = apply(s.value, map))
    case other => throw new NotImplementedError(s"TODO: deal with $other")
  }})

}