package benchmarks.fifo.paper

/*
import chisel3._
import chiseltest._
import chiseltest.experimental.TestOptionBuilder._
import chiseltest.internal.{VerilatorBackendAnnotation, WriteVcdAnnotation}
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.mutable
import scala.util.Random

class FifoPaperExampleUnitTest extends AnyFlatSpec with ChiselScalatestTester {
  val WithVCD = Seq(WriteVcdAnnotation)
  val NoVCD = Seq()
  val withVerilator = Seq(VerilatorBackendAnnotation)


  // Step 1: simple push with a unit test
  it should "push" in {
    test(new Fifo(8)).withAnnotations(WithVCD) { fifo =>
      fifo.io.dataIn.poke(123.U)
      fifo.io.pushDontPop.poke(true.B)
      fifo.io.valid.poke(true.B)
      fifo.clock.step()
    }
  }

  // Step 2: test to make sure we can read the value we pushed
  it should "push and pop" in {
    test(new Fifo(8)).withAnnotations(WithVCD) { fifo =>
      // push
      fifo.io.dataIn.poke(123.U)
      fifo.io.pushDontPop.poke(true.B)
      fifo.io.valid.poke(true.B)
      fifo.clock.step()
      // pop
      fifo.io.pushDontPop.poke(false.B)
      fifo.io.valid.poke(true.B)
      fifo.clock.step()
      fifo.io.dataOut.expect(123.U)
    }
  }

  // Step 3: we move push and pop into function and call them multiple times
  def push(fifo: Fifo, data: BigInt): Unit = {
    fifo.io.dataIn.poke(data.U)
    fifo.io.pushDontPop.poke(true.B)
    fifo.io.valid.poke(true.B)
    fifo.clock.step()
  }
  def pop(fifo: Fifo, data: BigInt): Unit = {
    fifo.io.pushDontPop.poke(false.B)
    fifo.io.valid.poke(true.B)
    fifo.clock.step()
    fifo.io.dataOut.expect(data.U)
  }

  it should "push and pop multiple values" in {
    test(new Fifo(8)).withAnnotations(WithVCD) { fifo =>
      push(fifo, 111)
      push(fifo, 222)
      push(fifo, 333)
      pop(fifo, 111)
      pop(fifo, 222)
      pop(fifo, 333)
    }
  }

  // Step 4: we randomly push and pop
  it should "push and pop multiple random values" in {
    assertThrows[NoSuchElementException] {
      test(new Fifo(8)).withAnnotations(WithVCD) { fifo =>
        val queue = mutable.Queue[BigInt]()
        val random = new Random(0)

        // test 100 transactions
        (0 until 100).foreach { _ =>
          val pushDontPop = random.nextBoolean()
          if (pushDontPop) {
            val value = BigInt(32, random)
            queue.enqueue(value)
            push(fifo, value)
          } else {
            val value = queue.dequeue()
            pop(fifo, value)
          }
        }
      }
    }
  }

  // Step 5: only pop when queue is not empty
  it should "only pop when queue is not empty" in {
    assertThrows[org.scalatest.exceptions.TestFailedException] {
      test(new Fifo(8)).withAnnotations(WithVCD) { fifo =>
        val queue = mutable.Queue[BigInt]()
        val random = new Random(0)

        // test 100 transactions
        (0 until 100).foreach { _ =>
          val popEnabled = queue.nonEmpty
          val pushDontPop = random.nextBoolean() || !popEnabled
          if (pushDontPop) {
            val value = BigInt(32, random)
            queue.enqueue(value)
            push(fifo, value)
          } else {
            val value = queue.dequeue()
            pop(fifo, value)
          }
        }
      }
    }
  }

  // Step 6: only push when queue is not full
  it should "only push when queue is not full" in {
    test(new Fifo(8)).withAnnotations(WithVCD) { fifo =>
      val queue = mutable.Queue[BigInt]()
      val random = new Random(0)

      // test 100 transactions
      (0 until 100).foreach { _ =>
        val pushEnabled = queue.size < fifo.depth
        val popEnabled = queue.nonEmpty

        val enabled = Seq(pushEnabled, popEnabled).zipWithIndex.filter(_._1).map(_._2)
        assert(enabled.nonEmpty, "deadlock")
        choose(random, enabled) match {
          case 0 =>
            val value = BigInt(32, random)
            queue.enqueue(value)
            push(fifo, value)
          case 1 =>
            val value = queue.dequeue()
            pop(fifo, value)
        }
      }
    }
  }

  // Step 7: allow pop on empty fifo
  def pop2(fifo: Fifo, data: BigInt, dataValid: Boolean): Unit = {
    fifo.io.pushDontPop.poke(false.B)
    fifo.io.valid.poke(true.B)
    fifo.clock.step()
    if(dataValid) fifo.io.dataOut.expect(data.U)
  }

  it should "allow pop on empty fifo" in {
    test(new Fifo(8)).withAnnotations(NoVCD) { fifo =>
      val queue = mutable.Queue[BigInt]()
      val random = new Random(0)

      // test 100 transactions
      (0 until 100).foreach { _ =>
        val pushEnabled = queue.size < fifo.depth
        val popEnabled = true

        val enabled = Seq(pushEnabled, popEnabled).zipWithIndex.filter(_._1).map(_._2)
        assert(enabled.nonEmpty, "deadlock")
        choose(random, enabled) match {
          case 0 =>
            val value = BigInt(32, random)
            queue.enqueue(value)
            push(fifo, value)
          case 1 =>
            val valid = queue.nonEmpty
            val value = if(valid) queue.dequeue() else BigInt(0)
            pop2(fifo, value, valid)
        }
      }
    }
  }

  // Step 8: add idle transaction
  def idle(fifo: Fifo): Unit = {
    fifo.io.valid := 0.U
    fifo.clock.step()
  }

  it should "also support the idle transaction" in {
    test(new Fifo(8)).withAnnotations(NoVCD) { fifo =>
      val queue = mutable.Queue[BigInt]()
      val random = new Random(0)

      // test 100 transactions
      (0 until 100).foreach { _ =>
        val pushEnabled = queue.size < fifo.depth
        val popEnabled = true
        val idleEnabled = true

        val enabled = Seq(pushEnabled, popEnabled).zipWithIndex.filter(_._1).map(_._2)
        assert(enabled.nonEmpty, "deadlock")
        choose(random, enabled) match {
          case 0 =>
            val value = BigInt(32, random)
            queue.enqueue(value)
            push(fifo, value)
          case 1 =>
            if(queue.isEmpty) {
              pop2(fifo, 0, false)
            } else {
              val value = queue.dequeue()
              pop(fifo, value)
            }
          case 2 =>
            idle(fifo)
        }
      }
    }
  }




  def or(a: Boolean, b: Boolean): Boolean = a | b

  def choose[T](random: Random, choices: Seq[T]): T = {
    val index = random.nextInt(choices.length)
    choices(index)
  }
}
*/
