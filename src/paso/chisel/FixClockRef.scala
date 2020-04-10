package paso.chisel

import firrtl.{CDefMPort, ir}

// dirty hack to fix the clock reference for register ports in untimed modules
// should run on high firrtl
case class FixClockRef(clock: ir.Expression) {
  private def fixPort(p: CDefMPort): CDefMPort = {
    p.copy(exps = Seq(p.exps.head, clock))
  }

  private def onStmt(s: ir.Statement): ir.Statement = s match {
    case p : CDefMPort => fixPort(p)
    case other => other.mapStmt(onStmt)
  }
  def apply(c: ir.Circuit): ir.Circuit = {
    assert(c.modules.length == 1)
    c.copy(modules = Seq(c.modules.head.asInstanceOf[ir.Module].mapStmt(onStmt)))
  }

}
