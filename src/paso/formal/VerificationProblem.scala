// Copyright 2020-2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.formal

import Chisel.log2Ceil
import maltese.mc.{IsModelChecker, ModelCheckFail, ModelCheckSuccess, Signal, State, TransitionSystem, TransitionSystemSimulator}
import maltese.{mc, smt}
import paso.protocols._
import paso.{DebugOptions, ProofFullAutomaton, ProofIsolatedMethods, untimed}

import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable

case class UntimedModel(sys: mc.TransitionSystem, methods: Seq[untimed.MethodInfo]) {
  def name: String = sys.name
  def addPrefix(prefix: String): UntimedModel = copy(sys = sys.copy(name = prefix + name))
}
case class Spec(untimed: UntimedModel, ugraphs: Seq[Proto])
case class VerificationProblem(impl: TransitionSystem, spec: Spec, subspecs: Seq[Spec], invariants: TransitionSystem)

object VerificationProblem {
  def verify(problem: VerificationProblem, opt: paso.ProofOptions, dbg: DebugOptions, workingDir: Path): Unit = {
    assert(Files.exists(workingDir), s"Working dir `$workingDir` does not exist!")

    val checker = makeChecker(opt.modelChecker, dbg.printMCProgress)
    val solver = smt.solvers.Yices2()

    // connect the implementation to the global reset
    val impl = connectToReset(problem.impl)

    // turn subspecs into monitoring automatons
    val subspecs = problem.subspecs.map(s => makePasoAutomaton(s.untimed, s.ugraphs, solver, workingDir, true)._1)

    // turn spec into a monitoring automaton
    val (spec, _) = makePasoAutomaton(problem.spec.untimed, problem.spec.ugraphs, solver, workingDir, invert=false)

    // encode invariants (if any)
    val invariants = encodeInvariants(spec.name, problem.invariants)

    // for the base case we combine everything together with a reset
    val baseCaseSys = mc.TransitionSystem.combine("base",
      List(noFinalStep, generateBmcConditions(1), impl) ++ subspecs ++ List(spec, invariants))
    val baseCaseTask = VerificationTask("base", {
      val (s, t) = time(check(checker, baseCaseSys, kMax = 1, workingDir = workingDir, printSys = dbg.printBaseSys))
      (s, List(t))
    })

    // for the induction we start the automaton in its initial state and assume
    val startStates = List(startInInitState(spec.name, subspecs.map(_.name)))
    val inductionBeforeSpec = List(generateInductionConditions(), removeInit(impl)) ++ subspecs
    val inductionAfterSpec = List(invariants) ++ startStates

    val inductionTasks = opt.strategy match {
      case ProofFullAutomaton =>
        List(VerificationTask("induction", {
          val time = new Timer()
          val (spec, longestPath) = time(makePasoAutomaton(problem.spec.untimed, problem.spec.ugraphs, solver, workingDir, invert = false))
          val inductionStep = mc.TransitionSystem.combine("induction",
            List(finalStep(longestPath)) ++ inductionBeforeSpec ++ List(spec) ++ inductionAfterSpec)
          val s = time(check(checker, inductionStep, kMax = longestPath, workingDir = workingDir, printSys = dbg.printInductionSys))
          (s, time.getTimes)
        }))
      case ProofIsolatedMethods =>
        // generate a (for now) forking automaton for each method + associated protocol
        problem.spec.ugraphs.map { proto =>
          VerificationTask(s"induction ${proto.name}", {
            val time = new Timer()
            val localDir = makeSubDir(workingDir, proto.name)
            val (spec, longestPath) = time(makePasoAutomaton(problem.spec.untimed, List(proto), solver, localDir, invert = false))
            val inductionStep = mc.TransitionSystem.combine("induction",
              List(finalStep(longestPath)) ++ inductionBeforeSpec ++ List(spec) ++ inductionAfterSpec)
            val s = time(check(checker, inductionStep, kMax = longestPath, workingDir = localDir, printSys = dbg.printInductionSys))
            (s, time.getTimes)
          })
        }
    }

    // run verification tasks
    assert(TaskRunner.run(List(baseCaseTask)),
      s"Failed to proof ${impl.name} correct. Please consult the base-case VCD file in $workingDir")
    assert(TaskRunner.run(inductionTasks),
      s"Failed to proof ${impl.name} correct. Please consult the VCD files in $workingDir")

    // check all our simplifications
    assert(!opt.checkSimplifications, "Cannot check simplifications! (not implement)")
  }

  private def makeSubDir(workingDir: Path, name: String): Path = {
    val path = workingDir.resolve(name)
    if(!Files.exists(path)) {
      Files.createDirectory(path)
    }
    path
  }

  def bmc(problem: VerificationProblem, modelChecker: paso.SolverName, kMax: Int, dbg: DebugOptions, workingDir: Path): Unit = {
    assert(Files.exists(workingDir), s"Working dir `$workingDir` does not exist!")
    val resetLength = 1
    val checker = makeChecker(modelChecker, dbg.printMCProgress)
    val solver = smt.solvers.Yices2()

    // connect the implementation to the global reset
    val impl = connectToReset(problem.impl)

    // turn spec into a monitoring automaton
    val (spec, _) = makePasoAutomaton(problem.spec.untimed, problem.spec.ugraphs, solver, workingDir, invert=false)

    // encode invariants (if any)
    val invariants = encodeInvariants(spec.name, problem.invariants)

    // we do a reset in the beginning
    val bmcSys = mc.TransitionSystem.combine("bmc",
      List(noFinalStep, generateBmcConditions(resetLength), impl, spec, invariants))

    // call checker
    val success = check(checker, bmcSys, kMax + resetLength, workingDir, printSys = dbg.printBmcSys)
    assert(success, s"Found a disagreement between implementation and spec. Please consult ${bmcSys.name}.vcd")
  }

  private def makeChecker(name: paso.SolverName, printProgress: Boolean): IsModelChecker = name match {
    case paso.Btormc => new mc.BtormcModelChecker()
    case paso.CVC4 => new mc.SMTModelChecker(new smt.solvers.CVC4SMTLib(), printProgress = printProgress)
    case paso.Z3 => new mc.SMTModelChecker(new smt.solvers.Z3SMTLib(), printProgress = printProgress)
    case paso.Yices2 =>
      println("WARN: using the SMTLib interface to yices atm.")
      println("      The native bindings are still missing some features.")
      new mc.SMTModelChecker(new smt.solvers.Yices2SMTLib(), printProgress = printProgress)
      //new mc.SMTModelChecker(smt.solvers.Yices2())
    case paso.Uclid5 => mc.Uclid5PseudoMC
  }

  private def check(checker: IsModelChecker, sys: TransitionSystem, kMax: Int, workingDir: Path, printSys: Boolean = false, debug: Iterable[smt.BVSymbol] = List()): Boolean = {
    val checkerFile = workingDir.resolve(sys.name + checker.fileExtension)
    val vcdFile = workingDir.resolve(sys.name + ".vcd")

    val fullSys = if(debug.isEmpty) { sys } else { observe(sys, debug) }
    if(printSys) { println(fullSys.serialize) }
    val res = checker.check(fullSys, kMax = kMax, fileName = Some(checkerFile.toString))
    res match {
      case ModelCheckFail(witness) =>
        val sim = new TransitionSystemSimulator(fullSys)
        sim.run(witness, vcdFileName = Some(vcdFile.toString))
        println(s"${fullSys.name} fails!")
        false
      case ModelCheckSuccess() =>
        // println(s"${fullSys.name} works!")
        true
    }
  }


  private def makePasoAutomaton(untimed: UntimedModel, protos: Seq[Proto], solver: smt.Solver, workingDir: Path, invert: Boolean, doFork: Boolean = true): (TransitionSystem, Int) = {
    new AutomatonBuilder(solver, workingDir).run(untimed, protos, invert, doFork)
  }

  private def generateBmcConditions(resetLength: Int = 1): TransitionSystem = {
    val reset = generateInitialReset(resetLength)
    val invertAssert = mc.Signal("invertAssert", smt.False())
    reset.copy(name="BmcConditions", signals = reset.signals :+ invertAssert)
  }

  private def generateInitialReset(length: Int = 1): TransitionSystem = {
    assert(length >= 1)
    val counterBits = List(log2Ceil(length), 1).max
    val counterMax = smt.BVLiteral((BigInt(1) << counterBits) - 1, counterBits)
    val counter = smt.BVSymbol("resetCounter", counterBits)
    val counterNext = smt.BVIte(smt.BVEqual(counter, counterMax), counter, smt.BVOp(smt.Op.Add, counter, smt.BVLiteral(1, counterBits)))
    val state = State(counter, init=Some(smt.BVLiteral(0, counterBits)), next=Some(counterNext))
    val reset = Signal("notReset", smt.BVComparison(smt.Compare.GreaterEqual, counter, smt.BVLiteral(length, counterBits), signed = false))
    val notReset = Signal("reset", smt.BVNot(smt.BVSymbol("notReset", 1)))
    mc.TransitionSystem("reset", List(), List(state), List(reset, notReset))
  }

  private def generateInductionConditions(): TransitionSystem = {
    // during induction, the reset is disabled
    val reset = mc.Signal("reset", smt.BVLiteral(0, 1))
    val notReset = mc.Signal("notReset", smt.BVLiteral(1, 1))

    // the initial state is constrained with the invariants + the automaton state is 0
    val isInit = smt.BVSymbol("isInit", 1)
    val state = State(isInit, init = Some(smt.True()), next = Some(smt.False()))
    val invertAssert = mc.Signal("invertAssert", isInit)

    mc.TransitionSystem("InductionConditions", List(), List(state), List(reset, notReset, invertAssert))
  }

  private def startInInitState(specName: String, subspecNames: Iterable[String]): TransitionSystem = {
    val isInit = smt.BVSymbol("isInit", 1)
    // we start all automatons in their initial state
    val assumptions = (List(specName) ++ subspecNames).zipWithIndex.map { case (name, ii) =>
      Signal(s"initState$ii", smt.BVImplies(isInit, smt.BVSymbol(name + ".automaton.initState", 1)), mc.IsConstraint)
    }
    // if the main spec is in a start state, we require all subspecs to also be in a start state
    val mainStartState = smt.BVSymbol(specName + ".automaton.StartState", 1)
    val assertions = subspecNames.zipWithIndex.map { case (subName, ii) =>
      val subStartState = smt.BVSymbol(subName + ".automaton.StartState", 1)
      val assertion = smt.BVImplies(smt.BVAnd(notReset, mainStartState), subStartState)
      Signal(s"startState$ii", smt.BVNot(assertion), mc.IsBad)
    }
    mc.TransitionSystem("StartInInitState", List(), List(), assumptions ++ assertions)
  }

  // for induction we want to know when it is the last cycle
  private def finalStep(kMax: Int): TransitionSystem = {
    val bits = 8
    require(kMax < (BigInt(1) << bits))
    val stepCount = smt.BVSymbol("stepCount", bits)
    val st = mc.State(stepCount, init = Some(smt.BVLiteral(0, bits)), next = Some(smt.BVOp(smt.Op.Add, stepCount, smt.BVLiteral(1, bits))))
    val sig = mc.Signal("finalStep", smt.BVEqual(stepCount, smt.BVLiteral(kMax, bits)))
    mc.TransitionSystem("FinalStep", List(), List(st), List(sig))
  }

  private def noFinalStep: TransitionSystem = {
    mc.TransitionSystem("FinalStep", List(), List(), List(mc.Signal("finalStep", smt.False())))
  }

  private def connectToReset(sys: TransitionSystem): TransitionSystem =
    TransitionSystem.connect(sys, Map(sys.name + ".reset" ->  reset))

  private def encodeInvariants(specName: String, invariants: TransitionSystem): TransitionSystem = {
    val startState = smt.BVSymbol(specName + ".automaton.StartState", 1)
    val invertAssert = smt.BVSymbol("invertAssert", 1)
    val sys = TransitionSystem.connect(invariants, Map(
      invariants.name + ".reset" -> reset,
      invariants.name + ".enabled" -> smt.BVAnd(notReset, startState),
      invariants.name + ".invertAssert" -> invertAssert,
    ))
    val nonRandomInputs = sys.inputs.filterNot(isRandomInput(_))
    assert(nonRandomInputs.isEmpty, s"Unexpected inputs: ${nonRandomInputs.mkString(", ")}")
    sys
  }

  private def observe(sys: TransitionSystem, signals: Iterable[smt.BVSymbol]): TransitionSystem = {
    val oState = signals.map(s => mc.State(s.rename(s.name + "$o"), None, None))
    val constraints = signals.map(s => mc.Signal(s.name + "$eq", smt.BVEqual(s, s.rename(s.name + "$o")), mc.IsConstraint))
    sys.copy(states = sys.states ++ oState, signals = sys.signals ++ constraints)
  }

  private def removeInit(sys: TransitionSystem): TransitionSystem =
    sys.copy(states = sys.states.map(_.copy(init = None)))

  private val reset = smt.BVSymbol("reset", 1)
  private val notReset = smt.BVSymbol("notReset", 1)
}

private object isRandomInput {
  def apply(i: smt.BVSymbol): Boolean = {
    i.name.contains("rand_data") || i.name.contains("invalid")
  }
}

private class VerificationTask(val name: String, val run: () => (Boolean, List[Long]))
private object VerificationTask {
  def apply(name: String, run: => (Boolean, List[Long])): VerificationTask =
    new VerificationTask(name, () => run)
}

private object TaskRunner {
  private val Fail = "❌"
  private val Success = "✅"
  def run(tasks: Seq[VerificationTask]): Boolean = {
    tasks.map(runTask).reduce(_ && _)
  }
  private def runTask(t: VerificationTask): Boolean = {
    val (success, times) = t.run()
    val msg = (if(success) Success else Fail) + " " + t.name + " (" + timeStr(times) + ")"
    println(msg)
    success
  }
  private def timeStr(times: Seq[Long]): String = times match {
    case Nil => throw new RuntimeException("empty times!")
    case Seq(one) => timeWithUnits(one)
    case multiple =>
      val total: Long = multiple.sum
      multiple.map(timeWithUnits).mkString(" + ") + " = " + timeWithUnits(total)
  }
  private val prefixes = List("n", "μ", "m", "", "k", "M")
  private def timeWithUnits(nanos: Long): String = {
    var num = nanos.toDouble
    prefixes.foreach { p =>
      if (num < 1000.0) {
        return f"$num%1.2f${p}s"
      }
      num /= 1000.0
    }
    throw new RuntimeException(s"ran out of prefixes for : $nanos")
  }
}

private class Timer() {
  private val times = mutable.ListBuffer[Long]()
  def apply[T](f: => T): T = {
    val start = System.nanoTime()
    val r = f
    times.append(System.nanoTime() - start)
    r
  }
  def getTimes: List[Long] = times.toList
}

private object time {
  def apply[T](f: => T): (T, Long) = {
    val start = System.nanoTime()
    val r = f
    val delta = System.nanoTime() - start
    (r, delta)
  }
}