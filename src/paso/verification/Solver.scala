package paso.verification
import uclid.smt

trait Solver {
  val name: String
  val supportsQuantifiers: Boolean
  protected val ctx: smt.Context

  def callCount: Int = pCallCount
  private var pCallCount = 0

  def push(): Unit = ctx.push()
  def pop(): Unit = ctx.pop()
  def assert(e: smt.Expr): Unit = ctx.assert(e)
  def check(): smt.SolverResult = ctx.check()
  /** (define-fun ...) */
  def define(f: smt.DefineFun): Unit = {

  }
  /** (declare-fun ...)  */
  def declare(f: smt.Symbol): Unit = {

  }
  /** (declare-sort ...) */
  def declare(f: smt.UninterpretedType): Unit = {

  }

  def check(e: smt.Expr): smt.SolverResult = {
    ctx.push()
    ctx.assert(e)
    pCallCount += 1
    val res = ctx.check()
    ctx.pop()
    res
  }
}

class YicesInterface extends Solver  {
  override val name = "yices2"
  override val supportsQuantifiers: Boolean = false
  protected override val ctx = new smt.SMTLIB2Interface(List("yices-smt2", "--incremental")) {
    writeCommand("(set-logic QF_AUFBV)")

    override def getModel(): Option[smt.Model] = {
      return None
      // TODO
    }
  }
}

class CVC4Interface(quantifierFree: Boolean = true) extends Solver  {
  override val name = "cvc4"
  override val supportsQuantifiers: Boolean = !quantifierFree
  protected override val ctx = new smt.SMTLIB2Interface(List("cvc4", "--incremental", "--produce-models", "--lang", "smt2")) {
    if(quantifierFree) writeCommand("(set-logic QF_AUFBV)")
    else writeCommand("(set-logic AUFBV)")
  }
}

class Z3Interface extends Solver  {
  override val name = "z3"
  override val supportsQuantifiers: Boolean = true
  protected override val ctx = new smt.SMTLIB2Interface(List("z3", "-in"))
}