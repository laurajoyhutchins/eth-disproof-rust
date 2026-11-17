import RuntimeHeapKernels

@[extern "lr_heap_compare"] opaque compareHeap (a b : Nat) : Nat
@[extern "lr_heap_compare_nested"] opaque compareNested
  (a b stamp : Nat) : Nat

def main : IO Unit := do
  let edges : Array Nat := #[
    0, 1, 2, 7, 17, 901, 2^16, 2^32, 2^40, 2^60
  ]
  for a in edges do
    for b in edges do
      if compareHeap a b != 0 then
        throw <| IO.userError s!"generated heap/Lean C mismatch: {a}, {b}"
  IO.println "reader-generated-lean-c-heap=PASS"
  for a in edges do
    for b in edges do
      for stamp in #[0, 17, 901] do
        let rc := compareNested a b stamp
        if rc != 0 then
          throw <| IO.userError
            s!"nested retained Lean C/Rust mismatch ({a}, {b}, {stamp}): code {rc}"
  IO.println "reader-generated-lean-c-nested-retain=PASS"
