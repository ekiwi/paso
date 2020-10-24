// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.verification

import maltese.mc.{Signal, State, TransitionSystem}
import maltese.smt
import paso.untimed

case class UntimedModel(sys: TransitionSystem, methods: Seq[untimed.MethodInfo]) {
  def name: String = sys.name
  def addPrefix(prefix: String): UntimedModel = copy(sys = sys.copy(name = prefix + name))
}