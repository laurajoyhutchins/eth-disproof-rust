import RuntimeHeapKernels
import RuntimeHeapDelKernels

-- Host calls one original compiled Lean C function and the exact
-- Reader-generated Rust function. Inputs are small/tagged Nat values;
-- arbitrary-precision heap Nat comparison remains outside this witness.
@[extern "lr_heap_compare_source_del"] opaque compareSourceDel
  (a b oldStamp newStamp threshold shared : Nat) : Nat

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
  IO.println s!"reader-generated-source-del-lean-c=PASS cases={cases}"
