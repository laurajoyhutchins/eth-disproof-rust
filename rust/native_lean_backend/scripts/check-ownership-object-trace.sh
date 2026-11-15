#!/usr/bin/env bash
# Compare *same Lean source* object IDs and source RC at observable boundaries.
# C uses actual lean_object headers; Rust uses the one canonical source ledger.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LEAN_PREFIX:?Set LEAN_PREFIX to pinned Lean 4.34.1}"
export PATH="$LEAN_PREFIX/bin:$PATH"
export LEAN_PATH="$(pwd)/examples:$(pwd):$LEAN_PREFIX/lib/lean"
export LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean"
test "$(lean --version)" = 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'
test "$(rustc --version)" = 'rustc 1.99.1 (58cf8f9c3 2026-10-13)'
NATIVE_LIB="$(pwd)/target/release/liblean_rust_native_backend.so"
test -s "$NATIVE_LIB"
out="$(pwd)/artifacts/ownership-object-trace"
mkdir -p "$out"
rm -rf examples/ownership-object-trace-package
lean -o examples/OwnershipObjectTraceKernels.olean examples/OwnershipObjectTraceKernels.lean
lean --load-dynlib="$NATIVE_LIB" examples/OwnershipObjectTraceFixture.lean
for root in create identity select throughClosure; do
  grep -Fq "Generated directly from Lean IR declaration: OwnershipObjectTrace.$root" examples/ownership-object-trace-package/src/lib.rs || exit 1
done
(cd examples && lean -c "$out/OwnershipObjectTraceKernels.c" OwnershipObjectTraceKernels.lean)
(cd examples && lean -c "$out/OwnershipObjectTraceCDriver.c" OwnershipObjectTraceCDriver.lean)
leanc -O2 -o "$out/lean-c" "$out/OwnershipObjectTraceKernels.c" "$out/OwnershipObjectTraceCDriver.c" native/object_trace_probe.c
"$out/lean-c" > "$out/c.txt"
cat examples/ownership_object_trace_test.rs >> examples/ownership-object-trace-package/src/lib.rs
OWNERSHIP_OBJECT_TRACE_OUT="$out/rust.txt" env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH cargo test --offline --manifest-path examples/ownership-object-trace-package/Cargo.toml --lib source_object_trace_tests::trace -- --exact
test -s "$out/c.txt"
test -s "$out/rust.txt"
if ! cmp -s "$out/c.txt" "$out/rust.txt"; then
  echo "Lean C physical object trace differs from Rust logical source RC trace" >&2
  diff -u "$out/c.txt" "$out/rust.txt" >&2 || true
  exit 1
fi
{
  echo 'status=PASS_SAME_SOURCE_C_RUST_OBSERVED_OBJECT_ID_AND_RC'
  echo "revision=$(git rev-parse HEAD)"
  echo "lean=$(lean --version)"
  echo "rust=$(rustc --version)"
  echo 'checkpoint_count=6'
  echo 'source_heap_simulation=UNPROVED_BEYOND_OBSERVED_BOUNDARIES'
  sha256sum examples/OwnershipObjectTraceKernels.lean examples/OwnershipObjectTraceFixture.lean examples/OwnershipObjectTraceCDriver.lean examples/ownership_object_trace_test.rs native/object_trace_probe.c "$out/OwnershipObjectTraceKernels.c" examples/ownership-object-trace-package/src/lib.rs "$out/c.txt" "$out/rust.txt"
} > "$out/receipt.txt"
cat "$out/receipt.txt"
