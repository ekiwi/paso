package paso.verification
import uclid.smt

trait Solver {
  val name: String
  val supportsQuantifiers: Boolean
  protected val ctx: smt.SMTLIB2Interface

  def callCount: Int = pCallCount
  private var pCallCount = 0

  def push(): Unit = ctx.push()
  def pop(): Unit = ctx.pop()
  def assert(e: smt.Expr): Unit = ctx.assert(e)
  def check(produceModel: Boolean = true): smt.SolverResult = ctx.check(produceModel)
  /** (define-fun ...) */
  def define(f: smt.DefineFun): Unit = {
    require(!ctx.variables.contains(f.id.id))
    ctx.variables += (f.id.id -> f.id)
    val argString = f.args.map(a => s"(${a.id} ${a.typ})").mkString(" ")
    val expr = ctx.translateExpr(f.e, true)
    val cmd = s"(define-fun ${f.id} ($argString) ${f.e.typ} $expr)"
    ctx.writeCommand(cmd)
  }
  /** (declare-fun ...)  */
  def declare(f: smt.Symbol): Unit = {
    if(!ctx.variables.contains(f.id)) {
      ctx.variables += (f.id -> f)
      ctx.generateDeclaration(f)
    }
  }
  /** (declare-sort ...) */
  def declare(f: smt.UninterpretedType): Unit = {
    ctx.writeCommand(s"(declare-sort ${f.name} 0)")
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
  def getCtx: smt.Context = ctx
}

class Z3Interface extends Solver  {
  override val name = "z3"
  override val supportsQuantifiers: Boolean = true
  protected override val ctx = new smt.SMTLIB2Interface(List("z3", "-in"))
}