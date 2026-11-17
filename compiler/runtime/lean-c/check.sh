#!/usr/bin/env bash
# Pinned original Lean C versus Rust that holds real Lean runtime handles.
# No synthetic reference ledger and no claim of generated-Rust correspondence.
set -euo pipefail
cd "$(dirname "$0")/../.."
: "${LEAN_PREFIX:?Pinned Lean 4.34.1 distribution required}"
export PATH="$LEAN_PREFIX/bin:$PATH"
export LEAN_PATH="$(pwd)/examples:$LEAN_PREFIX/lib/lean"
export LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
test "$(lean --version)" = 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'
test "$(rustc --version)" = 'rustc 1.99.1 (58cf8f9c3 2026-10-13)'
out="$(pwd)/artifacts/lean-c-runtime"
mkdir -p "$out"
lean -o examples/OwnershipObjectTraceKernels.olean examples/OwnershipObjectTraceKernels.lean
(cd examples && lean -c "$out/OwnershipObjectTraceKernels.c" OwnershipObjectTraceKernels.lean)
lean -c "$out/RuntimeDriver.c" runtime/lean-c/RuntimeDriver.lean
rustc --edition=2021 -C panic=abort --crate-type staticlib -D warnings -O \
  runtime/lean-c/src/lib.rs -o "$out/liblean_c_rust.a"
leanc -O2 -o "$out/runtime-probe" \
  "$out/OwnershipObjectTraceKernels.c" "$out/RuntimeDriver.c" \
  runtime/lean-c/abi.c runtime/lean-c/reference.c "$out/liblean_c_rust.a"
"$out/runtime-probe" | tee "$out/trace.txt"
grep -Fx 'lean-c-runtime-adapter=PASS' "$out/trace.txt"
{
  echo 'status=PASS_PINNED_LEAN_C_FFI_OWNERSHIP_BOUNDARY'
  echo "source_revision=$(git rev-parse HEAD)"
  echo "lean=$(lean --version)"
  echo "rust=$(rustc --version)"
  echo 'independent_original_lean_C_kernel=OwnershipObjectTrace.create'
  echo 'rust_handles=real_lean_C_heap_and_reference_counts'
  echo 'borrowed_field_lifetime=Rust_type_bounded'
  echo 'input_pairs=3'
  echo 'generated_Rust_emitter_integration=NOT_YET_ESTABLISHED'
  echo 'physical_semantic_equivalence=NOT_PROVED'
  sha256sum examples/OwnershipObjectTraceKernels.lean \
    runtime/lean-c/RuntimeDriver.lean runtime/lean-c/abi.c \
    runtime/lean-c/reference.c runtime/lean-c/src/lib.rs \
    "$out/OwnershipObjectTraceKernels.c" "$out/RuntimeDriver.c" \
    "$out/trace.txt"
} > "$out/receipt.txt"
cat "$out/receipt.txt"
