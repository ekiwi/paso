package chisel3.hacks

import chisel3._
import chisel3.aop.Aspect
import chisel3.internal.Builder


/** exposes some of the InjectingAspect magic for people who do not want the resulting firrtl to be appended to the parent module  **/
object ElaborateInContextOfModule {
  def apply(ctx: RawModule, gen: () => Unit, submoduleRefs: Boolean = false): firrtl.CircuitState = {
    val (chiselIR, _) = Builder.build(Module(new ModuleAspect(ctx) {
      override def desiredName: String = ctx.name
      ctx match {
        case x: MultiIOModule  => withClockAndReset(x.clock, x.reset) { gen() }
        case _: RawModule => gen()
      }
    }))
    firrtl.CircuitState(Aspect.getFirrtl(chiselIR), chiselIR.annotations.map(_.toFirrtl))
  }
}