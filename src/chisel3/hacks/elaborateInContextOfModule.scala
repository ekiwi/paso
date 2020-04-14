package chisel3.hacks

import chisel3._
import chisel3.aop.Aspect
import chisel3.internal.Builder
import chisel3.internal.firrtl._
import firrtl.annotations.Annotation

/** exposes some of the InjectingAspect magic for people who do not want the resulting firrtl to be appended to the parent module  **/
object elaborateInContextOfModule {
  def apply(ctx: RawModule, gen: () => Unit): (firrtl.ir.Circuit, Seq[Annotation]) = {
    val (chiselIR, _) = Builder.build(Module(new ModuleAspect(ctx) {
      ctx match {
        case x: MultiIOModule => withClockAndReset(x.clock, x.reset) { gen() }
        case x: RawModule => gen()
      }
    }))
    (Aspect.getFirrtl(chiselIR), chiselIR.annotations.map(_.toFirrtl))
  }
  def apply(ctx0: RawModule, ctx1: RawModule, name: String, gen: () => Unit): (firrtl.ir.Circuit, Seq[Annotation])  = {
    val (chiselIR, _) = Builder.build(Module(new ModuleDoubleAspect(ctx0, ctx1, name) {
      ctx0 match {
        case x: MultiIOModule => withClockAndReset(x.clock, x.reset) { gen() }
        case x: RawModule => gen()
      }
    }))
    val pp = prefixNames(Set(ctx0.name, ctx1.name)).run(chiselIR)
    (Aspect.getFirrtl(pp), chiselIR.annotations.map(_.toFirrtl))
  }
}

/** Replace nodes with absolute references if the element parent is part of {prefixes} */
case class prefixNames(prefixes: Set[String]) {
  case class FakeId(ref: Arg) extends chisel3.internal.HasId {
    override def toNamed = ???
    override def toTarget = ???
    override def toAbsoluteTarget = ???
    override def getRef: Arg = ref
    override def getOptionRef: Option[Arg] = Some(ref)
  }

  private def onNode(node: Node): Node = {
    val new_ref: Arg = node.id.getRef match {
      case a: Slot => onArg(a)
      case a: Index => onArg(a)
      case m: ModuleIO => Ref(s"${m.mod.getRef.name}.${m.name}")
      case r: Ref =>
        val pathName = node.id.pathName
        val parentPathName = node.id.parentPathName
        if (prefixes.contains(parentPathName)) {
          Ref(pathName)
        } else {
          r
        }
    }
    Node(FakeId(new_ref))
  }

  private def onArg(arg: Arg): Arg = arg match {
    case a : Node => onNode(a)
    case a : Slot  => a.copy(imm=onNode(a.imm))
    case a : Index => a.copy(imm=onArg(a.imm))
    case a : ModuleIO => throw new NotImplementedError(s"TODO: $a")
    case other => other
  }

  private def onCommand(com: Command): Command = com match {
    case DefPrim(info, id, op, args @_*) => DefPrim(info, id, op, args.map(onArg):_*)
    case Connect(info, loc, exp) => Connect(info, onNode(loc), onArg(exp))
    case WhenBegin(info, pred) => WhenBegin(info, onArg(pred))
    case ConnectInit(info, loc, exp) => ConnectInit(info, onNode(loc), onArg(exp))
    case p : DefMemPort[Data] =>
      p.copy(source = onNode(p.source), index = onArg(p.index), clock = onArg(p.clock))
    case other => other
  }

  private def onComponent(c: Component): Component = c match {
    case mm : DefModule => mm.copy(commands = mm.commands.map(onCommand))
    case other => other
  }

  def run(c: Circuit): Circuit = {
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