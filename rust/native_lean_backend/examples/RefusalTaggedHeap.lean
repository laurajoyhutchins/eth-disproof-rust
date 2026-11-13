import NativeRust

namespace RefusalTaggedHeap
  inductive Boxed where
    | mk (payload : UInt64)
  def get : Boxed → UInt64
    | .mk x => x
end RefusalTaggedHeap

#native_rust_closure RefusalTaggedHeap.get as "heap_get" to "examples/rejected_tagged_heap.rs"
