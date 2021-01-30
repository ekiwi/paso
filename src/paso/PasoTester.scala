// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso

import chisel3.RawModule
import org.scalatest._

import java.io.File
import scala.util.DynamicVariable

/** interface to integrate with scala test */
trait PasoTester extends PasoBaseTester with Assertions with TestSuiteMixin {
  this: TestSuite =>

  // the following code is mostly copied from chiseltest:
  protected def getTestName: String = {
    val ctx = scalaTestContext.value.getOrElse(
      throw new RuntimeException("No test context found! Make sure you are in a unittest.")
    )
    sanitizeFileName(ctx.name)
  }
  private def sanitizeFileName(name: String): String = {
    name.replaceAll(" ", "_").replaceAll("\\W+", "") // sanitize name
  }

  // Provide test fixture data as part of 'global' context during test runs
  private val scalaTestContext = new DynamicVariable[Option[NoArgTest]](None)

  abstract override def withFixture(test: NoArgTest): Outcome = {
    require(scalaTestContext.value.isEmpty)
    scalaTestContext.withValue(Some(test)) {
      super.withFixture(test)
    }
  }
}


trait PasoBaseTester {
  // the best way to get a test name depends on the testing framework used
  protected def getTestName: String
  private def getTestDir: String = "test_run_dir" + File.separator + getTestName

  def test[I <: RawModule](impl: => I): PasoImpl[I] = PasoImpl(() => impl, () => getTestDir)
}