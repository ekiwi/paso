// Copyright (c) 2017, Sanjit A. Seshia, Rohit Sinha and Pramod Subramanyan.
// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// this file originated from the UCLID5 Verification and Synthesis Engine

package maltese.smt.solvers.uclid

import scala.concurrent.SyncChannel
import scala.collection.JavaConverters._
import com.typesafe.scalalogging.Logger

class InteractiveProcess(args: List[String], saveInput: Boolean=false) {
  val logger = Logger(classOf[InteractiveProcess])

  // create the process.
  val cmdLine = (args).asJava
  val builder = new ProcessBuilder(cmdLine)
  builder.redirectErrorStream(true)
  val process = builder.start()
  val out = process.getInputStream
  val in = process.getOutputStream
  var exitValue : Option[Int] = None

  // stores what we've written to the interactive process so far
  var inputString = ""
  override def toString = inputString

  // channels for input and output.
  val inputChannel = new SyncChannel[Option[String]]()
  val outputChannel = new SyncChannel[Option[String]]()

  // Is this the best way of telling if a process is alive?
  def isAlive : Boolean = {
    process.isAlive
  }

  // Some helper functions.
  private def stringToBytes(str: String): Array[Byte] = str.map(_.toChar).toCharArray.map(_.toByte)
  private def bytesToString(bytes: Array[Byte]) = new String(bytes)


  // Write to the process's input stream.
  def writeInput(str: String): Unit = {
    logger.debug("-> {}", str)
    in.write(stringToBytes(str))
    if (saveInput) inputString += str
  }
  // Close stdin, this may cause the process to exit.
  def finishInput(): Unit = {
    in.flush()
    inputString = ""
    in.close()
  }
  // Read from the process's output stream.
  def readOutput() : Option[String] = {
    inputString = ""
    in.flush()
    var done = false
    while (!done) {
      if (!isAlive) {
        done = true
        logger.debug("Process dead")
      }
      val numAvail = out.available()
      if (numAvail == 0) {
        Thread.sleep(5)
      } else {
        val bytes = Array.ofDim[Byte](numAvail)
        val numRead = out.read(bytes, 0, numAvail)
        val string = bytesToString ({
          if (numRead == numAvail) {
            bytes
          } else {
            bytes.slice(0, numRead)
          }
        })
        logger.debug("<- {}", string)

        return Some(string)
      }
    }
    None
  }
  // Kill the process.
  def kill(): Unit = process.destroy()
}
