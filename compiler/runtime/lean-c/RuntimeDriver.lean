import OwnershipObjectTraceKernels

-- Lean's own compiled IO main initializes the C runtime.
@[extern "lr_runtime_crosscheck"] opaque runtimeCrosscheck : Nat → Nat

def main : IO Unit := do
  for n in #[0, 17, 901] do
    if runtimeCrosscheck n != 0 then
      throw <| IO.userError s!"Lean C runtime adapter disagrees with original source at {n}"
  IO.println "lean-c-runtime-adapter=PASS"
