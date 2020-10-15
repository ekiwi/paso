# Multiplier Protocol

The multiplier extension module from the PicoRV32 project has an
interesting protocol which uses some of our unique features:
- there is a bounded loop that polls `io.ready` to see if the operation is done
- one the operation is done we need to set valid to false immediatly
  which was previously disallowed since we treated path conditions
  and expect calls the same


## Protocol Source

```scala
  def mulProtocol(io: PCPI, clock: Clock, op: String, rs1: UInt, rs2: UInt, rd: UInt): Unit = {
    val instr = ("b" + "0000001" + "0000000000" + op + "00000" + "0110011").U

    io.valid.set(true.B)
    io.insn.set(instr)
    println(s"instruction: ${instr.litValue()}")
    io.rs1.set(rs1)
    io.rs2.set(rs2)
    io.wr.expect(false.B)
    io.ready.expect(false.B)
    clock.step()
    do_while(!io.ready.get(), max=70) {
      clock.step()
    }
    io.valid.set(false.B)
    io.rd.expect(rd)
    io.wr.expect(true.B)
    clock.step()
  }

```


## Protocol Goto Program
```
module mulProtocol :
  input clock : Clock
  input reset : UInt<1>
  output PicoRV32Mul.io_valid : UInt<1>
  output PicoRV32Mul.io_insn : UInt<32>
  output PicoRV32Mul.io_rs1 : UInt<32>
  output PicoRV32Mul.io_rs2 : UInt<32>
  input PicoRV32Mul.io_wr : UInt<1>
  input PicoRV32Mul.io_rd : UInt<32>
  input PicoRV32Mul.io_doWait : UInt<1>
  input PicoRV32Mul.io_ready : UInt<1>
  input Multiplier.mul_arg_a : UInt<32>
  input Multiplier.mul_arg_b : UInt<32>
  input Multiplier.mul_ret : UInt<32>

  0:
  PicoRV32Mul.io_valid <= UInt<1>("h1") @[ProtocolSpec.scala 32:9]
  PicoRV32Mul.io_insn <= UInt<26>("h2000033") @[ProtocolSpec.scala 32:9]
  PicoRV32Mul.io_rs1 <= Multiplier.mul_arg_a @[ProtocolSpec.scala 32:9]
  PicoRV32Mul.io_rs2 <= Multiplier.mul_arg_b @[ProtocolSpec.scala 32:9]
  assert(clock, eq(PicoRV32Mul.io_wr, UInt<1>("h0")), UInt<1>("h1"), "") @[ProtocolSpec.scala 72:85]
  assert(clock, eq(PicoRV32Mul.io_ready, UInt<1>("h0")), UInt<1>("h1"), "") @[ProtocolSpec.scala 72:85]
  wire step : UInt<1> @[ProtocolSpec.scala 46:19]
  when eq(PicoRV32Mul.io_ready, UInt<1>("h0")) goto 1 else goto 2
  1:
  wire step_1 : UInt<1> @[ProtocolSpec.scala 46:19]
  when eq(PicoRV32Mul.io_ready, UInt<1>("h0")) goto 3 else goto 4
  2:
  PicoRV32Mul.io_valid <= UInt<1>("h0") @[ProtocolSpec.scala 32:9]
  assert(clock, eq(PicoRV32Mul.io_rd, Multiplier.mul_ret), UInt<1>("h1"), "") @[ProtocolSpec.scala 72:85]
  assert(clock, eq(PicoRV32Mul.io_wr, UInt<1>("h1")), UInt<1>("h1"), "") @[ProtocolSpec.scala 72:85]
  wire step_71 : UInt<1> @[ProtocolSpec.scala 46:19]
  3:
  wire step_2 : UInt<1> @[ProtocolSpec.scala 46:19]
  when eq(PicoRV32Mul.io_ready, UInt<1>("h0")) goto 5 else goto 6
  4:
  goto 2
  5:
  wire step_3 : UInt<1> @[ProtocolSpec.scala 46:19]
  when eq(PicoRV32Mul.io_ready, UInt<1>("h0")) goto 7 else goto 8
  6:
  goto 4
  7:
  wire step_4 : UInt<1> @[ProtocolSpec.scala 46:19]
  when eq(PicoRV32Mul.io_ready, UInt<1>("h0")) goto 9 else goto 10
  8:
  goto 6
  9:
  wire step_5 : UInt<1> @[ProtocolSpec.scala 46:19]
  when eq(PicoRV32Mul.io_ready, UInt<1>("h0")) goto 11 else goto 12

  [...]

  138:
  goto 136
  139:
  wire step_70 : UInt<1> @[ProtocolSpec.scala 46:19]
  assert(clock, eq(eq(PicoRV32Mul.io_ready, UInt<1>("h0")), UInt<1>("h0")), UInt<1>("h1"), "") @[ProtocolSpec.scala 72:85]
  goto 140
  140:
  goto 138
```


## Protocol Interpretation

```
SET PicoRV32Mul.io_valid <= 1'b1  @[ProtocolSpec.scala 32:9]
SET PicoRV32Mul.io_insn <= 32'x2000033  @[ProtocolSpec.scala 32:9]
SET PicoRV32Mul.io_rs1 <= Multiplier.mul_arg_a  @[ProtocolSpec.scala 32:9]
SET PicoRV32Mul.io_rs2 <= Multiplier.mul_arg_b  @[ProtocolSpec.scala 32:9]
ASSERT not(PicoRV32Mul.io_wr)  @[ProtocolSpec.scala 72:85]
ASSERT not(PicoRV32Mul.io_ready)  @[ProtocolSpec.scala 72:85]
STEP @ 0:6  @[ProtocolSpec.scala 46:19]
IF not(PicoRV32Mul.io_ready) GOTO 1 ELSE 2
STEP @ 1:0  @[ProtocolSpec.scala 46:19]

[...]

IF not(PicoRV32Mul.io_ready) GOTO 139 ELSE 140
STEP @ 139:0  @[ProtocolSpec.scala 46:19]
ASSERT not(not(PicoRV32Mul.io_ready))  @[ProtocolSpec.scala 72:85]

[...]

SET PicoRV32Mul.io_valid <= 1'b0  @[ProtocolSpec.scala 32:9]
ASSERT eq(PicoRV32Mul.io_rd, Multiplier.mul_ret)  @[ProtocolSpec.scala 72:85]
ASSERT PicoRV32Mul.io_wr  @[ProtocolSpec.scala 72:85]
STEP @ 2:3  @[ProtocolSpec.scala 46:19]

[...]
```





