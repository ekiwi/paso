package paso.random


import firrtl.ir
import paso.protocols.{Proto, ProtocolVisualization}
import paso.{DebugOptions, UntimedModule}
import treadle.TreadleTester

case class TestingProblem(untimed: UntimedModule, protocols: IndexedSeq[Proto], impl: TreadleTester, io: Seq[ir.Port])


object TestingProblem {
  private val seedGen = new scala.util.Random(0)

  def randomTest(problem: TestingProblem, kMax: Int, seed: Option[Long], dbg: DebugOptions): Unit = {
    // val dot = ProtocolVisualization.toDot(problem.protocols.head.graph, true)
    // ProtocolVisualization.showDot(dot)


    val s = seed.getOrElse(seedGen.nextLong())
    val guide = new RandomGuide(s)

    val inputs = problem.io.filter(_.direction == ir.Input)
      .map(p => p.name -> firrtl.getWidth(p.tpe).asInstanceOf[ir.IntWidth].width.toInt)
      .filterNot(i => Set("reset", "clock").contains(i._1))

    // reset untimed model and implementation
    val untimed = problem.untimed.getTester
    untimed.poke("reset", 1)
    untimed.step(1)
    untimed.poke("reset", 0)
    resetImpl(problem.impl, inputs, guide)

    val interpreter = new ConcreteProtocolInterpreter(
      problem.untimed.getTester, problem.protocols, problem.impl, guide, inputs
    )

    // we need this block in order to ensure that the VCD is written to disk before we crash
    try {
      var active: List[interpreter.Loc] = List()
      (0 until kMax).foreach { k =>
        // println(s"k=$k")
        active = interpreter.executeStep(active)
        problem.impl.step()
      }
    } catch {
      case a : AssertionError => throw a
    } finally {
      problem.impl.step()
      problem.impl.finish
    }

    // println(s"Successfully tested ${problem.untimed.name} for $kMax cycles and seed=$s")
  }

  private def resetImpl(impl: TreadleTester, inputs: Seq[(String, Int)], guide: TestGuide): Unit = {
    impl.poke("reset", 1)
    // randomize all other inputs
    inputs.foreach { case (name, bits) =>
      impl.poke(name, guide.chooseInput(name, bits))
    }
    impl.step()
    impl.poke("reset", 0)
  }


}

class RandomGuide(seed: Long) extends TestGuide {
  private val rand = new scala.util.Random(seed)
  override def chooseTransaction(enabled: IndexedSeq[Proto]): Proto = {
    val index = rand.nextInt(enabled.size)
    enabled(index)
  }
  override def chooseArg(name: String, bits: Int): BigInt = BigInt(bits, rand)
  override def chooseInput(name: String, bits: Int): BigInt = BigInt(bits, rand)
}