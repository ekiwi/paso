// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.protocols

abstract class ProtocolInterpreter(val protocol: Protocol) {
  def expect()

}

sealed trait ProtocolResult
case object ProtocolFail extends ProtocolResult
case object ProtocolSuccess extends ProtocolResult

class ConcreteProtocolInterpreter(protocol: Protocol) extends ProtocolInterpreter(protocol) {

  def run(methodIO: Map[String, BigInt]): ProtocolResult = {
    ProtocolFail
  }

}