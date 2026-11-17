import NativeRust
import RuntimeHeapKernels

-- One authoritative IR dependency closure and one emitter. The generated
-- Rust value runtime is selected at *Rust compile time*, not IR-lowering time.
#native_rust_package [
  RuntimeHeap.make,
  RuntimeHeap.first,
  RuntimeHeap.observe
] to "examples/lean-c-heap-package"
