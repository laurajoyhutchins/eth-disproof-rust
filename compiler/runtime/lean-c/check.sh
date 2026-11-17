#!/usr/bin/env bash
# First runtime bridge: C-backed Owned/Borrowed values plus exact Reader-emitted
# scalar Rust called by an original Lean executable in the same C runtime.
set -euo pipefail
cd "$(dirname "$0")/../.."
: "${LEAN_PREFIX:?Pinned Lean 4.34.1 distribution required}"
export PATH="$LEAN_PREFIX/bin:$PATH"
export LEAN_PATH="$(pwd)/proofs:$(pwd)/examples:$LEAN_PREFIX/lib/lean"
export LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
test "$(lean --version)" = 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'
test "$(rustc --version)" = 'rustc 1.99.1 (58cf8f9c3 2026-10-13)'
test -s artifacts/reader-rust-exec-plus.rs
test -s artifacts/reader-rust-exec-plus.expected
test -s proofs/ScalarFixture.olean
out="$(pwd)/artifacts/lean-c-runtime"
mkdir -p "$out"
lean -o examples/OwnershipObjectTraceKernels.olean examples/OwnershipObjectTraceKernels.lean
(cd examples && lean -c "$out/OwnershipObjectTraceKernels.c" OwnershipObjectTraceKernels.lean)
(cd proofs && lean -c "$out/ScalarFixture.c" ScalarFixture.lean)
lean -c "$out/RuntimeDriver.c" runtime/lean-c/RuntimeDriver.lean

# The Reader source bytes are produced and kernel-checked by
# proofs/ReaderRustStatement.lean earlier in the *same* exact-head gate.
# Link them verbatim, rather than translating a Lean expression again.
cat > "$out/combined.rs" <<EOF
#[path = "$(pwd)/runtime/lean-c/src/lib.rs"]
mod runtime_bridge;
#[allow(dead_code)]
mod emitted_reader {
    include!(r#"$(pwd)/artifacts/reader-rust-exec-plus.rs"#);
}
#[no_mangle]
pub extern "C" fn lr_reader_generated_plus(a: u64, b: u64) -> u64 {
    emitted_reader::certified_scalar(a, b)
}
EOF
rustc --edition=2021 -C panic=abort --crate-type staticlib -D warnings -O \
  "$out/combined.rs" -o "$out/liblean_c_rust.a"
leanc -O2 -o "$out/runtime-probe" \
  "$out/OwnershipObjectTraceKernels.c" "$out/ScalarFixture.c" \
  "$out/RuntimeDriver.c" runtime/lean-c/abi.c \
  runtime/lean-c/reference.c "$out/liblean_c_rust.a"
"$out/runtime-probe" | tee "$out/trace.txt"
grep -Fx 'lean-c-runtime-adapter=PASS' "$out/trace.txt"
grep -Fx 'lean-c-reader-generated-scalar=PASS' "$out/trace.txt"
{
  echo 'status=PASS_PINNED_LEAN_C_FFI_AND_READER_SCALAR_IN_C_HOST'
  echo "source_revision=$(git rev-parse HEAD)"
  echo "lean=$(lean --version)"
  echo "rust=$(rustc --version)"
  echo 'independent_original_lean_C_kernel=OwnershipObjectTrace.create'
  echo 'rust_handles=real_lean_C_heap_and_reference_counts'
  echo 'borrowed_field_lifetime=Rust_type_bounded'
  echo 'constructor_input_count=3'
  echo 'reader_source=ScalarFixture.plus'
  echo 'reader_emission=actual_pinned_compiler_IR'
  echo 'reader_scalar_compiled_in=original_Lean_C_runtime_process'
  echo 'reader_scalar_pair_count=100'
  echo 'generated_Rust_heap_runtime_integration=NOT_YET_ESTABLISHED'
  echo 'physical_semantic_equivalence=NOT_PROVED'
  sha256sum examples/OwnershipObjectTraceKernels.lean \
    proofs/ScalarFixture.lean artifacts/reader-rust-exec-plus.rs \
    runtime/lean-c/RuntimeDriver.lean runtime/lean-c/abi.c \
    runtime/lean-c/reference.c runtime/lean-c/src/lib.rs \
    "$out/OwnershipObjectTraceKernels.c" "$out/ScalarFixture.c" \
    "$out/RuntimeDriver.c" "$out/combined.rs" "$out/trace.txt"
} > "$out/receipt.txt"
cat "$out/receipt.txt"
