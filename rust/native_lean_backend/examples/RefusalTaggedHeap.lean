import NativeRust

namespace RefusalTaggedHeap
  inductive Boxed where
    | mk (left right : UInt64)

  -- Both fields survive the Lean compiler and require a real constructor
  -- allocation. A one-field source wrapper can be optimized to a scalar.
  def allocate (x y : UInt64) : Boxed := .mk x y
end RefusalTaggedHeap

#native_rust_closure RefusalTaggedHeap.allocate as "heap_allocate" to "examples/rejected_tagged_heap.rs"
