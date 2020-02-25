package chisel3.hacks

import chisel3._
import chisel3.aop.Aspect
import chisel3.internal.Builder
import firrtl.ir

/** exposes some of the InjectingAspect magic for people who do not want the resulting firrtl to be appended to the parent module  **/
object elaborateInContextOfModule {
  def apply(ctx: RawModule, gen: () => Unit): ir.Circuit = {
    val (chiselIR, _) = Builder.build(Module(new ModuleAspect(ctx) {
      ctx match {
        case x: MultiIOModule => withClockAndReset(x.clock, x.reset) { gen() }
        case x: RawModule => gen()
      }
    }))
    Aspect.getFirrtl(chiselIR)
  }
  def apply(ctx0: RawModule, ctx1: RawModule, name: String, gen: () => Unit): ir.Circuit = {
    val (chiselIR, _) = Builder.build(Module(new ModuleDoubleAspect(ctx0, ctx1, name) {
      ctx0 match {
        case x: MultiIOModule => withClockAndReset(x.clock, x.reset) { gen() }
        case x: RawModule => gen()
      }
    }))
    Aspect.getFirrtl(chiselIR)
  }
}

abstract class ModuleDoubleAspect private[chisel3] (m0: RawModule, m1: RawModule, name: String)
(implicit moduleCompileOptions: CompileOptions) extends RawModule {
  Builder.addAspect(m0, this)
  Builder.addAspect(m1, this)
  override def circuitName: String = m0.toTarget.circuit
  override def desiredName: String = name
  // TODO: make sure namespaces don't overlap and merge them to form a common namespace
  override val _namespace = m0._namespace
}