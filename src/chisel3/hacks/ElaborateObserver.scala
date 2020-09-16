package chisel3.hacks

import chisel3._
import chisel3.aop.Aspect
import chisel3.internal.{Builder, Namespace}
import chisel3.internal.firrtl._
import firrtl.annotations.{CircuitTarget, ReferenceTarget}

import scala.collection.mutable

/** elaborate into a module that can observe internal signals of the modules it is _observing_ */
object ElaborateObserver {
  def apply(observing: Iterable[RawModule], name: String, gen: () => Unit): (firrtl.CircuitState, Seq[ExternalReference])  = {
    val (chiselIR, _) = Builder.build(Module(new ObservingModule(observing, name) { gen() }))
    val prefix = prefixNames(observing.map(_.name).toSet)
    val pp = prefix.run(chiselIR)
    (firrtl.CircuitState(Aspect.getFirrtl(pp), chiselIR.annotations.map(_.toFirrtl)), prefix.getExternalRefs)
  }
}

/** Replace nodes with absolute references if the element parent is part of {prefixes} */
case class prefixNames(prefixes: Set[String]) extends FixNaming {
  override def fixName(parentPathNamePrefix: String, pathName: String): Option[String] = {
    if (prefixes.contains(parentPathNamePrefix)) Some(pathName) else None
  }
}

case class ExternalReference(name: String, path: Seq[String]) {
  def toTarget(circuit: CircuitTarget): ReferenceTarget = {
    assert(path.length == 2)
    circuit.module(path.head).ref(path(1))
  }
}

abstract class FixNaming {
  def fixName(parentPathNamePrefix: String, pathName: String): Option[String]

  case class FakeId(ref: Arg) extends chisel3.internal.HasId {
    override def toNamed = ???
    override def toTarget = ???
    override def toAbsoluteTarget = ???
    override def getRef: Arg = ref
    override def getOptionRef: Option[Arg] = Some(ref)
  }

  def getExternalRefs: Seq[ExternalReference] = externalReferences.toSeq
  private val externalReferences = mutable.LinkedHashSet[ExternalReference]()

  private def onNode(node: Node): Node = {
    val new_ref: Arg = node.id.getRef match {
      case a: Slot => onArg(a)
      case a: Index => onArg(a)
      case m: ModuleIO => Ref(s"${m.mod.getRef.name}.${m.name}")
      case r: Ref =>
        val pathName = node.id.pathName
        val parentPathName = node.id.parentPathName
        val parentPathNamePrefix = parentPathName.split('.').headOption.getOrElse(parentPathName)
        fixName(parentPathNamePrefix, pathName) match {
          case Some(name) =>
            externalReferences.add(ExternalReference(name, pathName.split('.')))
            Ref(name)
          case None => r
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
    case p : DefMemPort[_] =>
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

abstract class ObservingModule private[chisel3](observing: Iterable[RawModule], name: String)
                                               (implicit moduleCompileOptions: CompileOptions) extends MultiIOModule {
  observing.foreach { o => Builder.addAspect(o, this) }
  override def circuitName: String = name
  override def desiredName: String = name
  // make sure that no signal can collide with the name of the modules that we are observing
  private val reservedNames = observing.map(_.name)
  override val _namespace = new Namespace(reservedNames.toSet)
}