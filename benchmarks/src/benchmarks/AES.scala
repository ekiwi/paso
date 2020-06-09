// Copyright 2020, SiFive, Inc
// released under Apache License Version 2.0
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package benchmarks

import paso._
import aes._
import chisel3._

object AESOneRound extends App {
  Paso(new OneRound)(new TinyAESRoundProtocol(_)).proof()
}

object AESFinalRound extends App {
  Paso(new FinalRound)(new TinyAESRoundProtocol(_)).proof()
}

object AESExpandKey extends App {
  StaticTables.rcon.foreach { ii =>
    val rc = ii.U(8.W)
    Paso(new ExpandKey128(rc))(new TinyAESExpandKeyProtocol(_)).proof()
  }
}

object AES extends App {
  Paso(new TinyAES128)(new TinyAESProtocol(_))(new SubSpecs(_, _) {
    replace(impl.finalRound)(new TinyAESRoundProtocol(_)).bind(spec.finalRound)
    impl.rounds.foreach(r => replace(r)(new TinyAESRoundProtocol(_)).bind(spec.round))
    impl.expandKey.zip(spec.expand).foreach { case (i, s) => replace(i)(new TinyAESExpandKeyProtocol(_)).bind(s) }
  }).proof(Paso.MCYices2)
}