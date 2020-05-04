// Copyright 2020 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package paso.chisel.passes

import firrtl.annotations.{Annotation, CircuitName, ComponentName, ModuleName, ReferenceTarget}
import firrtl.transforms.TopWiring.TopWiringAnnotation
import firrtl.{AnnotationSeq, ir}

import scala.collection.mutable

class ExposeSubModules(c: ir.Circuit, toBeReplaced: Set[String]) {
  private val mods = c.modules.collect{ case m: ir.Module => m.name -> m}.toMap
  case class ExposedPort(name: String, tpe: ir.Type, wire: ReferenceTarget)
  private val annos = mutable.ArrayBuffer[Annotation]()
  private val toplevel = ModuleName(c.main, CircuitName(c.main))

  private def exposeInstance(prefix: String, info: ir.Info, name: String, tpe: ir.Type): ir.Statement = {
    val p = prefix.replace('.', '_')
    // TODO: we cannot use toplevel when we want to support unreplace submodules
    annos.append(TopWiringAnnotation(ComponentName(name, toplevel), p))
    ir.Block(Seq(ir.DefWire(info, name, tpe), ir.IsInvalid(info, firrtl.WRef(name, tpe))))
  }

  private def onInstance(prefix: String, d: firrtl.WDefInstance): ir.Statement = {
    val doReplace = toBeReplaced.contains(prefix + d.name)
    if(doReplace) {
      exposeInstance(prefix, d.info, d.name, d.tpe)
    } else {
      throw new NotImplementedError("TODO: support submodules that are NOT replaced!")
      d.mapStmt(onStmt(prefix, _))
    }
  }

  private def onStmt(prefix: String, s: ir.Statement): ir.Statement = s match {
    case _ : ir.DefInstance =>
      throw new RuntimeException("Expected a working instance since we need to know the reference type!")
    case d : firrtl.WDefInstance => onInstance(prefix, d)
    case other => other.mapStmt(onStmt(prefix, _))
  }

  def apply(): (ir.Circuit, AnnotationSeq) = {
    val main = mods(c.main)
    val newBody = onStmt(c.main + ".", main.body)
    // TODO: support submodules that are not replaced
    val newC = c.copy(modules = Seq(main.copy(body = newBody)))
    (newC, annos)
  }
}
