import NativeRust
import RuntimeHeapDelKernels

-- This target is a real final-IR dependency closure. It is not a handwritten
-- `source_del` test host. The caller records an explicit refusal if the
-- canonical Reader cannot yet lower its join and ownership instructions.
#native_rust_package [
  RuntimeHeapDel.rebuildOrExtractByPayload
] to "examples/lean-c-del-package"
