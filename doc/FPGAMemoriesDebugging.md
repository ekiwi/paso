# Debugging Log for the FPGA Memores

## 2020-04-16: Trying to verify a 2W / 4R memory

- 14:55 after fixing some bugs in paso, the model checker runs and returns
  with a failing property:

```
b1: (not (=> (= __counter (_ bv1 1))
  (and (and (and
    (=> Untimed2W4RMemory.rw.rw_outputs_readData0.valid (= LVTMemory.io_read_0_data Untimed2W4RMemory.rw.rw_outputs_readData0))
    (=> Untimed2W4RMemory.rw.rw_outputs_readData1.valid (= LVTMemory.io_read_1_data Untimed2W4RMemory.rw.rw_outputs_readData1)))
    (=> Untimed2W4RMemory.rw.rw_outputs_readData2.valid (= LVTMemory.io_read_2_data Untimed2W4RMemory.rw.rw_outputs_readData2)))
    (=> Untimed2W4RMemory.rw.rw_outputs_readData3.valid (= LVTMemory.io_read_3_data Untimed2W4RMemory.rw.rw_outputs_readData3)))))
with
  __counter := 1,
  Untimed2W4RMemory.rw.rw_outputs_readData0.valid := 1,
  Untimed2W4RMemory.rw.rw_outputs_readData0 := 1042867826
  LVTMemory.io_read_0_data := 908650098,
  Untimed2W4RMemory.rw.rw_outputs_readData1.valid := 0,
  Untimed2W4RMemory.rw.rw_outputs_readData1 := 4025772749,
  LVTMemory.io_read_1_data := 3486804685,
  Untimed2W4RMemory.rw.rw_outputs_readData2.valid := 1,
  Untimed2W4RMemory.rw.rw_outputs_readData2 := 4025772749,
  LVTMemory.io_read_2_data := 4025772749,
  Untimed2W4RMemory.rw.rw_outputs_readData3.valid := 1,
  Untimed2W4RMemory.rw.rw_outputs_readData3 := 3486804685,
  LVTMemory.io_read_3_data := 3486804685,
```

- 14:58 after some formating, we see that there is a problem on read port 0:
  the read should be valid, however, the data does not match
- going to the wave form to debug now:
  - we see that the read address is 4
  - location 4 was not valid at the beginning of the transaction
  - it seems like it is valid at the end though (see counter example above)
  - thus there probably was a write to location 4
  - this is confirmed in the wave form: both write ports get address 4
    which should invalidate the location
  - thus it seems like in our spec, if there is a write conflict,
    we invalidate the location written to, but still return a value
    if we read from the same address! (15:06)
- 15:09: changed spec and verification passes after 80s:

```
-  data := in.writeData0
+  // if there is a write-write collision, the result is undefined
+  when(in.writeAddr0 === in.writeAddr1) {
+    data := DontCare
+  } .otherwise {
+    data := in.writeData0
+  }

```

