package paso.verification
import uclid.smt

trait Solver {
  val name: String
  protected val ctx: smt.Context

  def callCount: Int = pCallCount
  private var pCallCount = 0

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
  protected override val ctx = new smt.SMTLIB2Interface(List("yices-smt2", "--incremental")) {
    writeCommand("(set-logic QF_AUFBV)")

    override def getModel(): Option[smt.Model] = {
      return None
      // TODO
    }
  }
}

class CVC4Interface extends Solver  {
  override val name = "cvc4"
  protected override val ctx = new smt.SMTLIB2Interface(List("cvc4", "--incremental", "--produce-models"))
}

class Z3Interface extends Solver  {
  override val name = "z3"
  protected override val ctx = new smt.SMTLIB2Interface(List("z3", "-in"))
}