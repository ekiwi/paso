package chisel3.hacks

import chisel3._
import chisel3.aop.Aspect
import chisel3.internal.Builder
import chisel3.internal.firrtl._

/** exposes some of the InjectingAspect magic for people who do not want the resulting firrtl to be appended to the parent module  **/
object elaborateInContextOfModule {
  def apply(ctx: RawModule, gen: () => Unit): firrtl.ir.Circuit = {
    val (chiselIR, _) = Builder.build(Module(new ModuleAspect(ctx) {
      ctx match {
        case x: MultiIOModule => withClockAndReset(x.clock, x.reset) { gen() }
        case x: RawModule => gen()
      }
    }))
    Aspect.getFirrtl(chiselIR)
  }
  def apply(ctx0: RawModule, ctx1: RawModule, name: String, gen: () => Unit): firrtl.ir.Circuit = {
    val (chiselIR, _) = Builder.build(Module(new ModuleDoubleAspect(ctx0, ctx1, name) {
      ctx0 match {
        case x: MultiIOModule => withClockAndReset(x.clock, x.reset) { gen() }
        case x: RawModule => gen()
      }
    }))
    val pp = prefixNames(chiselIR)
    Aspect.getFirrtl(chiselIR)
  }
}

object prefixNames {
  private def onNode(node: Node): Node = {
    node
  }
  private def onArg(arg: Arg): Arg = arg match {
    case n : Node => onNode(n)
    case other => other
  }

  private def onCommand(com: Command): Command = com match {
    case DefPrim(info, id, op, args @_*) => DefPrim(info, id, op, args.map(onArg):_*)
    case Connect(info, loc, exp) => Connect(info, onNode(loc), exp)
    case other => other
  }

  private def onComponent(c: Component): Component = c match {
    case mm : DefModule => mm.copy(commands = mm.commands.map(onCommand))
    case other => other
  }

  def apply(c: Circuit): Circuit = {
    c.copy(components = c.components.map(onComponent))
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