import NativeRust
import BenchmarkKernels

-- Exact same executable declarations that the Lean C backend compiles.
#native_rust_package [
  BenchmarkKernels.arrayStep,
  BenchmarkKernels.closureStep,
  BenchmarkKernels.natStep,
  BenchmarkKernels.natAccumulate
] to "artifacts/bench-matrix/generated-package"
