package spec

import chisel3._
import paso._
import impl._
import org.scalatest._
import paso.chisel.Elaboration
import paso.verification.VerificationProblem

/** Simply returns the input unmodified */
class Identity[D <: Data](typ: D) extends UntimedModule {
  val id = fun("id").in(typ).out(typ){ (in, out) => out := in }
  val idle = fun("idle"){}
}

class VariableLatencyExamplesSpec {

}
