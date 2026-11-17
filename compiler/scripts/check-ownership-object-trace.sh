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
for root in create identity select throughClosure createNested; do
  grep -Fq "Generated directly from Lean IR declaration: OwnershipObjectTrace.$root" examples/ownership-object-trace-package/src/lib.rs || exit 1
done
(cd examples && lean -c "$out/OwnershipObjectTraceKernels.c" OwnershipObjectTraceKernels.lean)
(cd examples && lean -c "$out/OwnershipObjectTraceCDriver.c" OwnershipObjectTraceCDriver.lean)
leanc -O2 -o "$out/lean-c" "$out/OwnershipObjectTraceKernels.c" "$out/OwnershipObjectTraceCDriver.c" native/object_trace_probe.c
cat examples/ownership_object_trace_test.rs >> examples/ownership-object-trace-package/src/lib.rs
# Mutation controls must demonstrate that a pooled-count checker cannot
# confuse the first and second allocation or a retained descendant.
python3 scripts/check-object-identity-transfers.py --self-test
for inputs in "0 1" "17 23" "901 702"; do
  read -r first second <<< "$inputs"
  "$out/lean-c" "$first" "$second" | grep '^TRACE ' > "$out/c-$first-$second.txt"
  OWNERSHIP_OBJECT_TRACE_A="$first" OWNERSHIP_OBJECT_TRACE_B="$second" \
  OWNERSHIP_OBJECT_TRACE_OUT="$out/rust-$first-$second.txt" \
  env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
    cargo test --offline --manifest-path examples/ownership-object-trace-package/Cargo.toml --lib source_object_trace_tests::trace -- --exact
  test -s "$out/c-$first-$second.txt"
  test -s "$out/rust-$first-$second.txt"
  # The two-identity audit is stricter than whole-file byte agreement:
  # it requires the physical direct-call and branch-selection object IDs,
  # counts, and allocation separation to be correct on EACH backend.
  python3 scripts/check-object-identity-transfers.py \
    "$out/c-$first-$second.txt" "$out/rust-$first-$second.txt"
  if ! cmp -s "$out/c-$first-$second.txt" "$out/rust-$first-$second.txt"; then
    echo '--- source function C entry points ---' >&2
    grep -n -A 10 -E 'l_OwnershipObjectTrace_(create|identity|select|throughClosure)\\(' "$out/OwnershipObjectTraceKernels.c" | head -110 >&2 || true
    echo '--- source function Rust entry points ---' >&2
    grep -n -A 12 -E 'fn (create|identity|select|throughClosure|__lean_.*identity)' examples/ownership-object-trace-package/src/lib.rs | head -110 >&2 || true
    echo "Lean C physical object trace differs from Rust logical source RC trace at $inputs" >&2
    diff -u "$out/c-$first-$second.txt" "$out/rust-$first-$second.txt" >&2 || true
    exit 1
  fi
done
{
  echo 'status=PASS_SAME_SOURCE_C_RUST_OBSERVED_OBJECT_ID_AND_RC'
  echo "revision=$(git rev-parse HEAD)"
  echo "lean=$(lean --version)"
  echo "rust=$(rustc --version)"
  echo 'checkpoint_count=10'
  echo 'direct_second_object_identity=CHECKED'
  echo 'branch_selected_object_identity=CHECKED'
  echo 'cross_object_credit_conservation=MODEL_ONLY'
  echo 'nested_destructor_cascade=grandchild_and_direct_sibling'
  echo 'retained_descendant_counts=CHECKED_AFTER_ROOT_RELEASE'
  echo 'runtime_input_pairs=3'
  echo 'source_heap_simulation=UNPROVED_BEYOND_OBSERVED_BOUNDARIES'
  sha256sum examples/OwnershipObjectTraceKernels.lean examples/OwnershipObjectTraceFixture.lean examples/OwnershipObjectTraceCDriver.lean examples/ownership_object_trace_test.rs native/object_trace_probe.c scripts/check-object-identity-transfers.py "$out/OwnershipObjectTraceKernels.c" examples/ownership-object-trace-package/src/lib.rs "$out"/c-*.txt "$out"/rust-*.txt
} > "$out/receipt.txt"
cat "$out/receipt.txt"
