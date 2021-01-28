package paso.random


import firrtl.ir
import paso.{DebugOptions, UntimedModule}
import treadle.TreadleTester

case class TestingProblem(untimed: UntimedModule, protocols: IndexedSeq[ProtocolDesc], impl: TreadleTester, io: Seq[ir.Port])


object TestingProblem {
  private val seedGen = new scala.util.Random(0)

  def randomTest(problem: TestingProblem, kMax: Int, seed: Option[Long], dbg: DebugOptions): Unit = {
    val s = seed.getOrElse(seedGen.nextLong())
    val guide = new RandomGuide(s)

    val inputs = problem.io.filter(_.direction == ir.Input)
      .map(p => p.name -> firrtl.getWidth(p.tpe).asInstanceOf[ir.IntWidth].width.toInt)

    val interpreter = new ConcreteProtocolInterpreter(
      problem.untimed.getTester, problem.protocols, problem.impl, guide, inputs
    )

    var active: List[interpreter.Loc] = List()
    (0 until kMax).foreach { i =>
      active = interpreter.executeStep(active)
    }

    println(s"Successfully tested ${problem.untimed.name} for $kMax cycles and seed=$s")
  }


}

class RandomGuide(seed: Long) extends TestGuide {
  private val rand = new scala.util.Random(seed)
  override def chooseTransaction(enabled: IndexedSeq[ProtocolDesc]): ProtocolDesc = {
    val index = rand.nextInt(enabled.size)
    enabled(index)
  }
  override def chooseArg(name: String, bits: Int): BigInt = BigInt(bits, rand)
  override def chooseInput(name: String, bits: Int): BigInt = BigInt(bits, rand)
}