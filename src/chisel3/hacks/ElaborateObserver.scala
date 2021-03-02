package chisel3.hacks

import chisel3._
import chisel3.aop.Aspect
import chisel3.experimental.BaseModule
import chisel3.internal.{Builder, Namespace, DynamicContext}
import chisel3.internal.firrtl._
import firrtl.AnnotationSeq
import firrtl.annotations.{CircuitTarget, IsModule, ReferenceTarget}

import scala.collection.mutable

/** elaborate into a module that can observe internal signals of the modules it is _observing_ */
object ElaborateObserver {
  def apply(observing: Iterable[RawModule], name: String, gen: () => Unit, annos: AnnotationSeq = List()): (firrtl.CircuitState, Seq[ExternalReference])  = {
    ensureUniqueCircuitNames(observing)
    val ctx = new DynamicContext(annos)
    val (chiselIR, mod) = Builder.build(Module(new ObservingModule(observing, name) { gen() }), ctx)
    val prefix = new FixNamings(observing.map(_.name).toSet, mod._namespace)
    val pp = prefix.run(chiselIR)
    (firrtl.CircuitState(Aspect.getFirrtl(pp), chiselIR.annotations.map(_.toFirrtl)), prefix.getExternalRefs)
  }
  private def ensureUniqueCircuitNames(observing: Iterable[RawModule]): Unit = {
    val others = mutable.HashMap[String, RawModule]()
    observing.foreach { o =>
      assert(!others.contains(o.name), f"Cannot have more than one observed circuit named ${o.name}!")
      others(o.name) = o
    }
  }
}

/**
 * Represents a signal that is observed by an externally elaborated module (aka the observer).
 * @param signal observed signal
 * @param nameInObserver name of signal inside the observer (will be inside a bundle named for signal.circuit)
 */
case class ExternalReference(signal: ReferenceTarget, nameInObserver: String)

class FixNamings(val topLevelModules: Set[String], namespace: Namespace) {

  case class FakeId(ref: Arg) extends chisel3.internal.HasId {
    override def toNamed = ???
    override def toTarget = ???
    override def toAbsoluteTarget = ???
    override def getRef: Arg = ref
    override def getOptionRef: Option[Arg] = Some(ref)
  }

  def getExternalRefs: Seq[ExternalReference] = externalReferences.toSeq
  private val externalReferences = mutable.LinkedHashSet[ExternalReference]()

  // maps an observed signal to its internal name
  private val mappings = mutable.HashMap[String, String]()
  private def getInternalName(path: Iterable[String]): String = {
    mappings.getOrElseUpdate(path.mkString("."), namespace.name(path.mkString("_")))
  }

  private def onNode(node: Node): Node = {
    val new_ref: Arg = node.id.getRef match {
      case a: Slot => onArg(a)
      case a: Index => onArg(a)
      case m: ModuleIO => m
      case r: Ref =>
        val path = node.id.pathName.split('.')
        val isCrossModuleRef = topLevelModules.contains(path.head)
        if(isCrossModuleRef) {
          // create a unique name inside the observer module
          val nameInObserver = getInternalName(path)
          val ref = node.id.toAbsoluteTarget.asInstanceOf[ReferenceTarget]
          externalReferences.add(ExternalReference(ref, nameInObserver))
          Node(FakeId(Ref(nameInObserver)))
        } else { r }
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
    case Verification(op, sourceInfo, clock, predicate, message) =>
      Verification(op, sourceInfo, clock, onArg(predicate), message)
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
                                               (implicit moduleCompileOptions: CompileOptions) extends Module {
  // we want to be able to not only observe the top-level module, but also all of their child modules
  private def addAspect(m : BaseModule): Unit = {
    Builder.addAspect(m, this)
    chisel3.aop.Select.instances(m).foreach(addAspect)
  }
  observing.foreach(addAspect)

  override def circuitName: String = name
  override def desiredName: String = name
  // make sure that no signal can collide with the name of the modules that we are observing
  private val reservedNames = observing.map(_.name)
  override val _namespace = new Namespace(reservedNames.toSet)
}