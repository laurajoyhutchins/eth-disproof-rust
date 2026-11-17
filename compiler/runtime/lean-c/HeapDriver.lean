import RuntimeHeapKernels

@[extern "lr_heap_compare"] opaque compareHeap (a b : Nat) : Nat

def main : IO Unit := do
  let edges : Array Nat := #[
    0, 1, 2, 7, 17, 901, 2^16, 2^32, 2^40, 2^60
  ]
  for a in edges do
    for b in edges do
      if compareHeap a b != 0 then
        throw <| IO.userError s!"generated heap/Lean C mismatch: {a}, {b}"
  IO.println "reader-generated-lean-c-heap=PASS"
