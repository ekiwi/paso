// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package object paso {
  type ProtocolSpec[+S <: UntimedModule] = paso.protocols.ProtocolSpec[S]
}
