import OwnershipObjectTraceKernels
import ScalarFixture

-- Lean's compiled IO entry point initializes and owns the C runtime.
@[extern "lr_runtime_crosscheck"] opaque runtimeCrosscheck : Nat → Nat
-- This symbol is compiled from actual Reader-emitted Rust, not a manually
-- translated implementation of ScalarFixture.plus.
@[extern "lr_reader_generated_plus"] opaque readerGeneratedPlus
  (x y : UInt64) : UInt64

def main : IO Unit := do
  for n in #[0, 17, 901] do
    if runtimeCrosscheck n != 0 then
      throw <| IO.userError s!"Lean C ownership bridge disagrees at {n}"
  IO.println "lean-c-runtime-adapter=PASS"
  let edges : Array UInt64 := #[
    0, 1, 2, 3, 7, 42,
    UInt64.ofNat (2^32),
    UInt64.ofNat (2^63),
    UInt64.ofNat (2^64 - 2),
    UInt64.ofNat (2^64 - 1)
  ]
  for x in edges do
    for y in edges do
      if readerGeneratedPlus x y != ScalarFixture.plus x y then
        throw <| IO.userError s!"Reader-generated Rust disagrees with Lean/C at {x}, {y}"
  IO.println "lean-c-reader-generated-scalar=PASS"
