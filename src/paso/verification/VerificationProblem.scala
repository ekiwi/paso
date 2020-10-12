// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

// contains data structures used for verification
// mostly language neutral (aka Chisel independent)

package paso.verification

import paso.chisel.{SMTHelper, SMTHelpers, SMTSimplifier}
import paso.untimed
import uclid.smt
import uclid.smt.Expr

import scala.collection.mutable

// Verification Graph
sealed trait VerificationNode {
  val next: Seq[VerificationNode]
  val methods: Set[String]
  def isFinal: Boolean = next.isEmpty
  def isBranchPoint: Boolean = next.length > 1
}

sealed trait IONode {
  val constraints: Seq[smt.Expr]
  val mappings: Seq[ArgumentEq]
  val hasGuardedMappings: Boolean = false
  lazy val constraintExpr: smt.Expr = SMTHelper.conjunction(constraints)
  lazy val mappingExpr: smt.Expr = {
    val e = if(hasGuardedMappings) { mappings.map(_.toGuardedExpr()) } else { mappings.map(_.toExpr()) }
    SMTHelper.conjunction(e)
  }
}

case class StepNode(next: Seq[InputNode], methods: Set[String], id: Int, isFork: Boolean) extends VerificationNode
case class InputNode(next: Seq[OutputNode], methods: Set[String], constraints: Seq[smt.Expr] = Seq(), mappings: Seq[ArgumentEq]= Seq()) extends VerificationNode with IONode
case class OutputNode(next: Seq[StepNode], methods: Set[String], constraints: Seq[smt.Expr] = Seq(), mappings: Seq[ArgumentEq]= Seq()) extends VerificationNode with IONode {
  override val hasGuardedMappings: Boolean = true
}

trait Assertion { def toExpr: smt.Expr }
case class BasicAssertion(guard: smt.Expr, pred: smt.Expr) extends Assertion {
  override def toExpr: Expr = SMTHelper.implies(guard, pred)
}
case class ForAllAssertion(variable: smt.Symbol, start: Int, end: Int, guard: smt.Expr, pred: smt.Expr) extends Assertion {
  override def toExpr: Expr = {
    val max = 1 << SMTHelper.getBits(variable.typ)
    val isFullRange = start == 0 && end == max
    val g = if(isFullRange) { guard } else {
      val lower = SMTHelper.cmpConst(smt.BVGEUOp, variable, start)
      val upper = SMTHelper.cmpConst(smt.BVLEUOp, variable, end-1)
      SMTHelper.and(guard, SMTHelper.and(lower, upper))
    }
    SMTHelper.forall(Seq(variable), SMTHelper.implies(g, pred))
  }
}

case class Spec(untimed: UntimedModel, protocols: Map[String, StepNode])
case class Subspec(instance: String, ioSymbols: Seq[smt.Symbol], spec: Spec, binding: Option[String])
case class VerificationProblem(impl: smt.TransitionSystem, spec: Spec, subspecs: Seq[Subspec],
                               invariances: Seq[Assertion], mapping: Seq[Assertion])

object VerificationProblem {
  def verify(problem: VerificationProblem, opt: paso.ProofOptions): Unit = {
    // reset any simplifications that might be globally cached
    SMTSimplifier.clear()
    // check to see if the mappings contain quantifiers
    val quantifierFree = !(problem.mapping ++ problem.invariances).exists(_.isInstanceOf[ForAllAssertion])
    // first we need to make sure to properly namespace all symbols in the Verification Problem
    val p = NamespaceIdentifiers(problem)

    val tasks = Seq(
      new VerifyMapping(opt.baseCaseSolver, quantifierFree),
      new VerifyBaseCase(opt.baseCaseSolver),
      new VerifyMethods(opt.oneMethodAtATime, opt.modelChecker, quantifierFree))
    tasks.foreach(_.run(p))

    // check all our simplifications
    if(opt.checkSimplifications) {
      val cvc4 = new CVC4Interface(quantifierFree = false)
      SMTSimplifier.verifySimplifications(cvc4.getCtx)
    }
  }

  def bmc(problem: VerificationProblem, solver: paso.SolverName, kMax: Int): Unit = {
    assert(problem.mapping.isEmpty)
    assert(problem.invariances.isEmpty)
    // reset any simplifications that might be globally cached
    SMTSimplifier.clear()
    // first we need to make sure to properly namespace all symbols in the Verification Problem
    val p = NamespaceIdentifiers(problem)
    new RunBmc(solver, kMax).run(p)
  }
}

class RunBmc(solver: paso.SolverName, kMax: Int) extends VerificationTask with SMTHelpers {
  val checker: smt.IsModelChecker = solver match {
    case paso.Btormc => smt.Btor2.createBtorMC()
    case paso.Z3 => new SMTModelChecker(new Z3Interface, SMTModelCheckerOptions.Performance)
    case paso.CVC4 => new SMTModelChecker(new CVC4Interface(quantifierFree = true), SMTModelCheckerOptions.Performance)
    case paso.Yices2 => new SMTModelChecker(new YicesInterface, SMTModelCheckerOptions.Performance)
  }

  override val solverName: String = checker.name

  private def runCheck(k: Int, sys: smt.TransitionSystem, foos: Seq[smt.DefineFun], uf: Seq[smt.Symbol]): (smt.ModelCheckResult, smt.TransitionSystemSimulator) = {
    val reducedSys = if(checker.supportsUF) { sys } else {
      assert(uf.isEmpty, s"Uninterpreted Functions are not supported by the model checker ${checker.name}")
      // beta reduce transition system (functions are not supported by btor)
      val beta = SMTBetaReduction(foos)
      sys.copy(
        states = sys.states.map(s => s.copy(init = s.init.map(beta(_)), next = s.next.map(beta(_)))),
        outputs = sys.outputs.map(o => (o._1, beta(o._2))),
        constraints = sys.constraints.map(beta(_)),
        bad = sys.bad.map(beta(_)),
        fair = sys.fair.map(beta(_)),
      )
    }
    val defined = if(checker.supportsUF) { foos } else { Seq() }

    //reducedSys.bad.zipWithIndex.foreach { case (b, i) => println(s"b$i: ${SMTSimplifier.simplify(b)}") }

    val res = checker.check(reducedSys, fileName=Some("test.btor"), kMax = k, defined = defined, uninterpreted = uf)
    val sim = new smt.TransitionSystemSimulator(reducedSys, functionDefinitions = defined)
    (res, sim)
  }
/*
  private def resolveBindings(subspecs: Seq[Subspec], topUntimed: UntimedModel): (Seq[smt.DefineFun], Seq[smt.Symbol]) = {
    val subSpecMethodFunctionDefinitions = subspecs.flatMap { sub =>
      sub.binding match {
        case Some(name) =>
          // find untimed submodule of the top level spec that we are bound to
          assert(topUntimed.sub.contains(name), s"Bound submodule $name not found. Maybe try: ${topUntimed.sub.keys.mkString(" ")}")
          val bound = topUntimed.sub(name)
          // ensure that we are binding equivalent specs
          assert(bound.methods.keys.toSet == sub.spec.untimed.methods.keys.toSet) // TODO: this doesn't really show that they are equivalent
          // define functions to alias with the functions of the spec this was bound to
          UntimedModel.functionDefAlias(sub.spec.untimed, bound)
        case None => UntimedModel.functionDefs(sub.spec.untimed)
      }
    }
    // remember which submodules should be modelled with UFs
    val boundSubModules = subspecs.flatMap(s => s.binding.toSeq).toSet
    val submoduleFoos = topUntimed.sub.filterNot(s => boundSubModules.contains(s._1)).flatMap(s => UntimedModel.functionDefs(s._2)).toSeq
    val boundSubmoduleFoos = topUntimed.sub.filter(s => boundSubModules.contains(s._1)).flatMap(s => UntimedModel.functionDefs(s._2))
    val boundValidFoos = boundSubmoduleFoos.filter(_.id.id.endsWith(".valid"))
    val submoduleUFs = boundSubmoduleFoos.filterNot(_.id.id.endsWith(".valid")).map(_.id).toSeq
    // for now we only support abstracted submodules if their output is always valid
    boundValidFoos.foreach(v => assert(v.e == tru, s"Only always valid methods can be turned into UFs. Not $v!"))

    (boundValidFoos.toSeq ++ subSpecMethodFunctionDefinitions ++ submoduleFoos, submoduleUFs)
  }

  private def ignoreBindings(subspecs: Seq[Subspec], topUntimed: UntimedModel): (Seq[smt.DefineFun], Seq[smt.Symbol]) = {
    subspecs.filter(_.binding.isDefined).foreach(s => println(s"WARN: ignoring binding of ${s.instance} to ${s.binding.get} because the backend does not support UFs!"))
    val subSpecMethodFunctionDefinitions = subspecs.flatMap { sub => UntimedModel.functionDefs(sub.spec.untimed) }
    val submoduleFoos = topUntimed.sub.flatMap(s => UntimedModel.functionDefs(s._2)).toSeq
    (subSpecMethodFunctionDefinitions ++ submoduleFoos, Seq())
  }
 */

  override protected def execute(p: VerificationProblem): Unit = {
    // first we need to merge the protocol graph to ensure that methods are independent
    // - independence in this case means that for common inputs, the expected outputs are not mutually exclusive
    val combined = p.spec.protocols.values.reduce(VerificationGraph.merge) // this will fail if methods are not independent

    // if there are subspecs, we need to generate a transition system simulating them
    val subTransitionsSystems = p.subspecs.map { sub =>
      val resetAssumption = VerificationTask.findReset(sub.ioSymbols).map(not).getOrElse(tru)
      NewVerificationAutomatonEncoder.run(sub.spec, sub.instance + ".", resetAssumption, switchAssumesAndGuarantees = true, initArchState = true)
    }

    // TODO
    /*
    val (foos, ufs) = if(checker.supportsUF) {
      resolveBindings(p.subspecs, p.spec.untimed)
    } else {
      ignoreBindings(p.subspecs, p.spec.untimed)
    }
    */

    // generate the toplevel transition system
    val resetAssumption = VerificationTask.findReset(p.impl.inputs).map(not).getOrElse(tru)
    // val toplevelFoos = UntimedModel.functionDefs(p.spec.untimed)
    val topTransitionSystem = NewVerificationAutomatonEncoder.run(p.spec, "", resetAssumption, switchAssumesAndGuarantees = false, initArchState = true)

    // add reset values to impl
    val resetState = VerificationTask.getResetState(p.impl)
    val simplResetState = resetState.mapValues(SMTSimplifier.simplify)
    // TODO: for now we ignore non constant resets
    val constantResetState = simplResetState.filter{ case (_, expr) => expr.isConstant }
    val initStates = p.impl.states.map{ s => assert(s.init.isEmpty); s.copy(init = constantResetState.get(s.sym)) }
    val initImpl = p.impl.copy(states= initStates)

    // combine systems
    val sys = smt.TransitionSystem.merge(initImpl, Seq(topTransitionSystem.sys) ++ subTransitionsSystems.map(_.sys))
    //sys.bad.zipWithIndex.foreach { case (b, i) => println(s"b$i: ${SMTSimplifier.simplify(b)}") }
    val (res, sim) = runCheck(kMax, sys, Seq(), Seq())

    // find failing property and print
    res match {
      case smt.ModelCheckFail(witness) =>
        println(s"Failed to verify ${p.impl.name.get} against ${p.spec.untimed.name}")
        sim.run(witness, Some("test.vcd"))
      case smt.ModelCheckSuccess() =>
    }

    assert(res.isSuccess, s"Failed to verify ${p.impl.name.get} against ${p.spec.untimed.name}")
  }
}

class VerifyMethods(oneAtATime: Boolean, solver: paso.SolverName, quantifierFree: Boolean) extends VerificationTask with SMTHelpers {
  val checker: smt.IsModelChecker = solver match {
    case paso.Btormc => smt.Btor2.createBtorMC()
    case paso.Z3 => new SMTModelChecker(new Z3Interface, SMTModelCheckerOptions.Performance)
    case paso.CVC4 => new SMTModelChecker(new CVC4Interface(quantifierFree), SMTModelCheckerOptions.Performance)
    case paso.Yices2 => new SMTModelChecker(new YicesInterface, SMTModelCheckerOptions.Performance)
  }

  override val solverName: String = checker.name

  private def runCheck(k: Int, sys: smt.TransitionSystem, foos: Seq[smt.DefineFun], uf: Seq[smt.Symbol]): (smt.ModelCheckResult, smt.TransitionSystemSimulator) = {
    val reducedSys = if(checker.supportsUF) { sys } else {
      assert(uf.isEmpty, s"Uninterpreted Functions are not supported by the model checker ${checker.name}")
      // beta reduce transition system (functions are not supported by btor)
      val beta = SMTBetaReduction(foos)
      sys.copy(
        states = sys.states.map(s => s.copy(init = s.init.map(beta(_)), next = s.next.map(beta(_)))),
        outputs = sys.outputs.map(o => (o._1, beta(o._2))),
        constraints = sys.constraints.map(beta(_)),
        bad = sys.bad.map(beta(_)),
        fair = sys.fair.map(beta(_)),
      )
    }
    val defined = if(checker.supportsUF) { foos } else { Seq() }

    val res = checker.check(reducedSys, fileName=Some("test.btor"), kMax = k, defined = defined, uninterpreted = uf)
    val sim = new smt.TransitionSystemSimulator(reducedSys, functionDefinitions = defined)
    (res, sim)
  }


  private def verifyMethods(p: VerificationProblem, proto: StepNode, methods: Seq[untimed.MethodInfo], foos: Seq[smt.DefineFun], ufs: Seq[smt.Symbol], sub: Seq[PasoAutomaton]): Unit = {
    //println(s"Trying to verify ${methods.keys.mkString(", ")} on ${p.spec.untimed.name}...")
    val check = new BoundedCheckBuilder(p.impl)

    //ShowDot(VerificationGraphToDot("proto", proto))

    // eliminate quantifiers by expansion (only the invariances and mappings are expected to contain quantifiers)
    val elim: smt.Expr => smt.Expr = if(checker.supportsQuantifiers) e => e else SMTExpandQuantifiers(_)

    // assume that reset is inactive
    VerificationTask.findReset(p.impl.inputs).foreach(r => check.assume(not(r)))
    // assume that invariances hold in the initial state
    p.invariances.foreach(i => check.assumeAt(0, elim(i.toExpr)))
    // assume that the mapping function holds in the initial state
    p.mapping.foreach(m => check.assumeAt(0, elim(m.toExpr)))
    // declare starting state
    p.spec.untimed.state.map(_.sym).foreach(check.declare)
    // declare method inputs
    // TODO
    // methods.values.flatMap(_.inputs).foreach(check.declare)
    // define method outputs
    // TODO
    /*
    methods.foreach { case (_, sem) =>
      sem.outputs.foreach { o => check.define(o.sym, o.expr) }
      sem.outputs.foreach { o => check.define(smt.Symbol(o.sym.id + ".valid", smt.BoolType), o.guard) }
    }
    // compute the results of all methods
    val method_state_subs = methods.map { case (name, sem) =>
      sem.updates.foreach{ o => check.define(o.sym.copy(id = o.sym.id + s".$name"), o.expr) }
      name -> sem.updates.map(_.sym).map(s => s -> s.copy(id = s.id + s".$name"))
    }
     */

    // encode the protocol tree
    val guards = Map[String, smt.Expr]() // TODO: methods.mapValues(_.guard)
    val final_edges = new VerificationTreeEncoder(check, guards).run(proto)

    // make sure that in any fork state, the mapping as well as the invariances hold
    final_edges.foreach { case ForkNode(ii, guard, method) =>
      // substitute any references to the state of the untimed model with the result of applying the method
      val subs: Map[smt.Expr, smt.Expr] = Map() // TODO: method_state_subs(method).toMap
      p.invariances.foreach(i => check.assertAt(ii, implies(guard, elim(i.toExpr))))
      p.mapping.map(substituteSmt(_, subs)).foreach(m => check.assertAt(ii, implies(guard, elim(m.toExpr))))
      // any subsystem needs to also be in a fork state
      sub.foreach(s => check.assertAt(ii, implies(guard, s.inForkState)))
    }

    val sys = smt.TransitionSystem.merge(check.getCombinedSystem, sub.map(_.sys))
    val (res, sim) = runCheck(check.getK, sys, foos, ufs)

    // find failing property and print
    res match {
      case smt.ModelCheckFail(witness) =>
        println(s"Failed to verify ${methods.map(_.name).mkString(", ")} on ${p.spec.untimed.name}")
        sim.run(witness, Some("test.vcd"))
      case smt.ModelCheckSuccess() =>
    }

    assert(res.isSuccess, s"Failed to verify ${methods.map(_.name).mkString(", ")} on ${p.spec.untimed.name}")
  }

  /*
  private def resolveBindings(subspecs: Seq[Subspec], topUntimed: UntimedModel): (Seq[smt.DefineFun], Seq[smt.Symbol]) = {
    val subSpecMethodFunctionDefinitions = subspecs.flatMap { sub =>
      sub.binding match {
        case Some(name) =>
          // find untimed submodule of the top level spec that we are bound to
          assert(topUntimed.sub.contains(name), s"Bound submodule $name not found. Maybe try: ${topUntimed.sub.keys.mkString(" ")}")
          val bound = topUntimed.sub(name)
          // ensure that we are binding equivalent specs
          assert(bound.methods.keys.toSet == sub.spec.untimed.methods.keys.toSet) // TODO: this doesn't really show that they are equivalent
          // define functions to alias with the functions of the spec this was bound to
          UntimedModel.functionDefAlias(sub.spec.untimed, bound)
        case None => UntimedModel.functionDefs(sub.spec.untimed)
      }
    }
    // remember which submodules should be modelled with UFs
    val boundSubModules = subspecs.flatMap(s => s.binding.toSeq).toSet
    val submoduleFoos = topUntimed.sub.filterNot(s => boundSubModules.contains(s._1)).flatMap(s => UntimedModel.functionDefs(s._2)).toSeq
    val boundSubmoduleFoos = topUntimed.sub.filter(s => boundSubModules.contains(s._1)).flatMap(s => UntimedModel.functionDefs(s._2))
    val boundValidFoos = boundSubmoduleFoos.filter(_.id.id.endsWith(".valid"))
    val submoduleUFs = boundSubmoduleFoos.filterNot(_.id.id.endsWith(".valid")).map(_.id).toSeq
    // for now we only support abstracted submodules if their output is always valid
    boundValidFoos.foreach(v => assert(v.e == tru, s"Only always valid methods can be turned into UFs. Not $v!"))

    (boundValidFoos.toSeq ++ subSpecMethodFunctionDefinitions ++ submoduleFoos, submoduleUFs)
  }

  private def ignoreBindings(subspecs: Seq[Subspec], topUntimed: UntimedModel): (Seq[smt.DefineFun], Seq[smt.Symbol]) = {
    subspecs.filter(_.binding.isDefined).foreach(s => println(s"WARN: ignoring binding of ${s.instance} to ${s.binding.get} because the backend does not support UFs!"))
    val subSpecMethodFunctionDefinitions = subspecs.flatMap { sub => UntimedModel.functionDefs(sub.spec.untimed) }
    val submoduleFoos = topUntimed.sub.flatMap(s => UntimedModel.functionDefs(s._2)).toSeq
    (subSpecMethodFunctionDefinitions ++ submoduleFoos, Seq())
  }
   */

  override protected def execute(p: VerificationProblem): Unit = {
    // first we need to merge the protocol graph to ensure that methods are independent
    // - independence in this case means that for common inputs, the expected outputs are not mutually exclusive
    val combined = p.spec.protocols.values.reduce(VerificationGraph.merge) // this will fail if methods are not independent

    // if there are subspecs, we need to generate a transition system simulating them
    val subTransitionsSystems = p.subspecs.map { sub =>
      val resetAssumption = VerificationTask.findReset(sub.ioSymbols).map(not).getOrElse(tru)
      NewVerificationAutomatonEncoder.run(sub.spec, sub.instance + ".", resetAssumption, switchAssumesAndGuarantees = true, initArchState = false)
    }

    // FIXME
    /*
    val (foos, ufs) = if(checker.supportsUF) {
      resolveBindings(p.subspecs, p.spec.untimed)
    } else {
      ignoreBindings(p.subspecs, p.spec.untimed)
    }
     */
    val (foos, ufs) = (List(), List())

    // we can verify each method individually or with the combined method graph
    if(oneAtATime) {
      p.spec.untimed.methods.foreach { m =>
        verifyMethods(p, p.spec.protocols(m.name), List(m), foos, ufs, subTransitionsSystems)
      }
    } else {
      verifyMethods(p, combined, p.spec.untimed.methods, foos, ufs, subTransitionsSystems)
    }

  }
}

class RefEqHashMap[A <: AnyRef, B] extends scala.collection.mutable.HashMap[A, B] {
  protected override def elemEquals(key1: A, key2: A): Boolean = (key1 eq key2)
}

class VerifyMapping(sol: paso.SolverName, quantifierFree: Boolean) extends VerificationTask with SMTHelpers with HasSolver {
  val solver = getSolver(sol, quantifierFree)
  override val solverName: String = solver.name

  override protected def execute(p: VerificationProblem): Unit = {
    if(p.mapping.isEmpty) return // early return for empty mapping
    val impl_states = p.impl.states.map(_.sym)
    val impl_init_const = conjunction(VerificationTask.getResetState(p.impl).map{ case (sym, value) => eq(sym, value)} )
    val spec_states = p.spec.untimed.state.map(_.sym)
    val spec_init_const = conjunction(p.spec.untimed.state.map{st => eq(st.sym, st.init.get)})
    val mapping_const = conjunction(p.mapping.map(_.toExpr))

    // The mapping check gets a lot easier because we require the untimed model to have all states initialized
    // to a concrete value, thus eliminating all quantifiers. (the non general solution)
    val use_general_solution = false
    if(use_general_solution) {
      try {
        // forall initial states of the implementation there exists an initial state in the specification for which the mapping holds
        val unmappable_impl = SMTSimplifier.simplify(and(impl_init_const, forall(spec_states, not(and(spec_init_const, mapping_const)))))

        val impl_res = check(unmappable_impl)
        assert(impl_res.isFalse, s"Found an implementation initial state for which there is no mapping: $impl_res")

        // forall initial states of the specification there exists an initial state in the implementation for which the mapping holds
        val unmappable_spec = SMTSimplifier.simplify(and(spec_init_const, forall(impl_states, not(and(impl_init_const, mapping_const)))))

        val spec_res = check(unmappable_spec)
        assert(spec_res.isFalse, s"Found a specification initial state for which there is no mapping: $spec_res")
      } catch {
        case e: uclid.Utils.AssertionError =>
          assert(e.getMessage.contains("unknown"))
          println(s"WARNING: cannot prove mapping correct: $solverName returned unknown")
      }
    } else {
      // With only a single initial specification state we need to show that for all initial implementation
      // states the mapping holds. We turn the universal into a existential query through the standard negation.
      val query = SMTSimplifier.simplify(and(and(impl_init_const, spec_init_const), not(mapping_const)))
      val res = check(query)
      assert(res.isFalse, s"Found a implementation initial state for which there is no mapping: $res")

    }
  }
}

class VerifyBaseCase(sol: paso.SolverName) extends VerificationTask with SMTHelpers with HasSolver {
  val solver = getSolver(sol, quantifierFree = true)
  override val solverName: String = solver.name

  override protected def execute(p: VerificationProblem): Unit = {
    val impl_init_const = conjunction(VerificationTask.getResetState(p.impl).map{ case (sym, value) => eq(sym, value)}.toSeq)
    val inv_const = conjunction(p.invariances.map(_.toExpr))

    // substitute implementation outputs in the invariants
    val outputSubs: Map[smt.Expr, smt.Expr] =  p.impl.outputs.map(o => smt.Symbol(o._1, o._2.typ)-> o._2).toMap
    val inv_const_sub = substituteSmt(inv_const, outputSubs)

    // make sure invariances hold after reset
    val hold = SMTSimplifier.simplify(implies(impl_init_const, inv_const_sub))
    val res = check(not(hold))
    assert(res.isFalse, s"FAIL: Invariances are not necessarily true after reset: ${res.model}")
  }
}

abstract class VerificationTask {
  val solverName: String
  protected def execute(p: VerificationProblem): Unit
  def run(p: VerificationProblem): Unit = {
    val start = System.nanoTime()
    execute(p)
    val end = System.nanoTime()
    println(s"Executed ${this.getClass.getSimpleName} with $solverName in ${(end - start)/1000/1000}ms")
  }
  protected def getSolver(sol: paso.SolverName, quantifierFree: Boolean): Solver = sol match {
    case paso.Btormc => throw new RuntimeException("btormc cannot be used to verify the base case or the mappings")
    case paso.Z3 => new Z3Interface
    case paso.Yices2 => assert(quantifierFree) ; new YicesInterface
    case paso.CVC4 => new CVC4Interface(quantifierFree)
  }
}

object VerificationTask {
  // TODO: don't hardcode reset
  def isReset(sym: smt.Symbol): Boolean = sym.id.endsWith(".reset") && sym.typ.isBool
  def findReset(symbols: Iterable[smt.Symbol]): Option[smt.Symbol] = symbols.find(isReset)
  /** starts in initial state and advances one step with reset = 1 and every other input with an arbitrary value */
  def getResetState(sys: smt.TransitionSystem): Map[smt.Symbol, smt.Expr] = {
    val inits = sys.states.map {
      case smt.State(sym, Some(init), _) => sym -> init
      case smt.State(sym, None, _) => sym -> smt.Symbol(sym.id + ".init", sym.typ)
    }.toMap
    val inputs = sys.inputs.map { sym => sym -> (if(isReset(sym)) smt.BooleanLit(true) else sym) }.toMap
    val subs: Map[smt.Expr, smt.Expr] = inits ++ inputs
    sys.states.map {
      case smt.State(sym, _, Some(next)) => sym -> substituteSmt(next, subs)
      case smt.State(sym, _, None) => sym -> smt.Symbol(sym.id + ".aux", sym.symbolTyp)
    }.toMap
  }
}