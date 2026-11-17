import RuntimeHeapKernels
import RuntimeHeapDelKernels

-- Host calls one original compiled Lean C function and the exact
-- Reader-generated Rust function. Inputs are small/tagged Nat values;
-- arbitrary-precision heap Nat comparison remains outside this witness.
@[extern "lr_heap_compare_source_del"] opaque compareSourceDel
  (a b oldStamp newStamp threshold shared : Nat) : Nat

-- The physical-operation oracle uses real Lean 4.34.1 C functions;
-- the borrowed dynamic heap Nat stays live across every checkpoint.
@[extern "lr_heap_trace_source_credits"] opaque traceSourceCredits
  (oldStamp : @& Nat) : Nat

def main : IO Unit := do
  let values : Array Nat := #[0, 1, 2, 7, 17, 901, 2^16, 2^32, 2^40, 2^60]
  let mut cases := 0
  for a in values do
    for b in #[0, 17, 901] do
      for oldStamp in #[0, 17, 901] do
        for threshold in #[a, a + 1] do
          for shared in #[0, 1] do
            let newStamp := oldStamp + 11
            let result := compareSourceDel a b oldStamp newStamp threshold shared
            if result != 0 then
              throw <| IO.userError
                s!"source-del original Lean C/Rust C mismatch a={a} b={b} old={oldStamp} new={newStamp} threshold={threshold} shared={shared}: code {result}"
            cases := cases + 1
  -- Force runtime heap Nat allocations: these stamps are not immediates,
  -- so the exclusive branch must physically decrement the old field.
  -- A dynamic, positive addition prevents reusing an immutable literal.
  for a in values do
    for b in #[0, 17, 901] do
      for base in #[(2^63 + 9 : Nat), 2^80 + 17, 2^128 + 5] do
        let heapStamp := base + a + 1
        for threshold in #[a, a + 1] do
          for shared in #[0, 1] do
            let result := compareSourceDel a b heapStamp 23 threshold shared
            if result != 0 then
              throw <| IO.userError
                s!"heap-stamp source-del mismatch a={a} b={b} threshold={threshold} shared={shared}: code {result}"
            cases := cases + 1
  IO.println s!"reader-generated-source-del-lean-c=PASS cases={cases}"
  -- The input must be a runtime-created, single-threaded heap Nat,
  -- not a compiler-persisted numeric literal with reference count zero.
  let runtimeSalt ← IO.monoMsNow
  let traceStamp := (2^128 + 7 : Nat) + runtimeSalt.toNat
  let traceResult := traceSourceCredits traceStamp
  if traceResult != 0 then
    throw <| IO.userError s!"Lean C physical step oracle refused: {traceResult}"
  IO.println "reader-source-shell-physical-checkpoints=RECORDED"
