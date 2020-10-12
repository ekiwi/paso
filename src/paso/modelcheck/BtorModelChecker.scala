// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.modelcheck

import java.io.PrintWriter

import scala.collection.mutable
import maltese.smt
import scala.sys.process._

class BtormcModelChecker extends ModelChecker {
  // TODO: check to make sure binary exists
  override val name: String = "btormc"
  override val supportsOutput: Boolean = false
  override def makeArgs(kMax: Int, inputFile: Option[String]): Seq[String] = {
    val prefix = if(kMax > 0) Seq("btormc", s"--kmax $kMax") else Seq("btormc")
    inputFile match {
      case None => prefix
      case Some(file) => prefix ++ Seq(s"$file")
    }
  }
  override protected def isFail(ret: Int, res: Seq[String]): Boolean = {
    assert(ret == 0, s"We expect btormc to always return 0, not $ret. Maybe there was an error:\n" + res.mkString("\n"))
    super.isFail(ret, res)
  }
}

class Cosa2ModelChecker extends ModelChecker {
  // TODO: check to make sure binary exists
  override val name: String = "cosa2"
  override val supportsOutput: Boolean = true
  override val supportsMultipleProperties: Boolean = false
  override def makeArgs(kMax: Int, inputFile: Option[String]): Seq[String] = {
    val base = Seq("cosa2", "--engine bmc")
    val prefix = if(kMax > 0) base ++ Seq(s"--bound $kMax") else base
    inputFile match {
      case None => throw new RuntimeException("cosa2 only supports file based input. Please supply a filename!")
      case Some(file) => prefix ++ Seq(s"$file")
    }
  }
  private val WrongUsage = 3
  private val Unknown = 2
  private val Sat = 1
  private val Unsat = 0
  override protected def isFail(ret: Int, res: Seq[String]): Boolean = {
    assert(ret != WrongUsage, "There was an error trying to call cosa2:\n"+res.mkString("\n"))
    val fail = super.isFail(ret, res)
    if(fail) { assert(ret == Sat) } else { assert(ret == Unknown) /* bmc only returns unknown because it cannot prove unsat */}
    fail
  }
}

abstract class ModelChecker extends IsModelChecker {
  override val name: String
  def makeArgs(kMax: Int, inputFile: Option[String] = None): Seq[String]
  val supportsOutput: Boolean
  val supportsMultipleProperties: Boolean = true
  override def check(sys: smt.TransitionSystem, kMax: Int = -1, fileName: Option[String] = None): ModelCheckResult = {
    val checkSys = if(supportsMultipleProperties) sys else sys.unifyProperties() //.unifyConstraints()
    fileName match {
      case None => checkWithPipe(checkSys, kMax)
      case Some(file) => checkWithFile(file, checkSys, kMax)
    }
  }

  /* called to check the results of the solver */
  protected def isFail(ret: Int, res: Seq[String]): Boolean = res.nonEmpty && res.head.startsWith("sat")

  private def checkWithFile(fileName: String, sys: smt.TransitionSystem, kMax: Int): ModelCheckResult = {
    val btorWrite = new PrintWriter(fileName)
    val lines = Btor2.serialize(sys, !supportsOutput)
    lines.foreach{l => btorWrite.println(l) }
    btorWrite.close()

    // execute model checker
    val cmd = makeArgs(kMax, Some(fileName)).mkString(" ")
    val stdout = mutable.ArrayBuffer[String]()
    val stderr = mutable.ArrayBuffer[String]()
    val ret = cmd ! ProcessLogger(stdout.append(_), stderr.append(_))
    if(stderr.nonEmpty) { println(s"ERROR: ${stderr.mkString("\n")}") }

    // write stdout to file for debugging
    val res: Seq[String] = stdout
    val resultFileName = fileName + ".out"
    val stdoutWrite = new PrintWriter(resultFileName)
    res.foreach(l => stdoutWrite.println(l))
    stdoutWrite.close()

    //print(cmd)
    //println(s" -> $ret")

    // check if it starts with sat
    if(isFail(ret, res)) {
      val witness = Btor2.readWitness(res)
      ModelCheckFail(witness)
    } else {
      ModelCheckSuccess()
    }
  }

  private def checkWithPipe(sys: smt.TransitionSystem, kMax: Int): ModelCheckResult = {
    val checker = new uclid.InteractiveProcess(makeArgs(kMax).toList)
    val lines = Btor2.serialize(sys, !supportsOutput)
    lines.foreach{l => checker.writeInput(l) ; println(l)}
    checker.finishInput()
    val res = checker.readOutput()
    res match {
      case None => ModelCheckSuccess()
      case Some(msg) =>
        val witness = Btor2.readWitness(res)
        ModelCheckFail(witness)
    }
  }
}