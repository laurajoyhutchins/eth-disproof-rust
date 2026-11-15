import NativeRust
import OwnershipObjectTraceKernels

#native_rust_package [
  OwnershipObjectTrace.create,
  OwnershipObjectTrace.identity,
  OwnershipObjectTrace.select,
  OwnershipObjectTrace.throughClosure
] to "examples/ownership-object-trace-package"
