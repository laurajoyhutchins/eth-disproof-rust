#!/usr/bin/env bash
# Exact emitted IR code, not reimplemented Rust, choosing physical Lean C
# objects at Rust compile time. Pinned external Lean C is the oracle.
set -euo pipefail
cd "$(dirname "$0")/../.."
: "${LEAN_PREFIX:?Set LEAN_PREFIX to pinned Lean 4.34.1}"
test -s "${NATIVE_LIB:?Build the canonical backend first}"
export PATH="$LEAN_PREFIX/bin:$PATH"
export LEAN_PATH="$(pwd)/examples:$(pwd):$LEAN_PREFIX/lib/lean"
export LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
test "$(lean --version)" = 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'
test "$(rustc --version)" = 'rustc 1.99.1 (58cf8f9c3 2026-10-13)'
out="$(pwd)/artifacts/lean-c-generated-heap"
mkdir -p "$out"
rm -rf examples/lean-c-heap-package
lean -o examples/RuntimeHeapKernels.olean examples/RuntimeHeapKernels.lean
lean --load-dynlib="$NATIVE_LIB" examples/RuntimeHeapFixture.lean
file=examples/lean-c-heap-package/src/lib.rs
test -s "$file"
for root in make first observe nest payload nestedFirst; do
  grep -Fq "Generated directly from Lean IR declaration: RuntimeHeap.$root" "$file" || {
    echo "Missing actual emitted source for RuntimeHeap.$root" >&2; exit 2;
  }
done
# The Rust functions and dependency closure are not edited. Only host ABI
# glue is appended, and the alternate runtime is built from an emitted cfg.
cp "$file" "$out/exact-emitter.rs"
cat "$file" runtime/lean-c/heap_host.rs > "$out/combined.rs"
rustc --edition=2021 --cfg 'feature="lean-c-runtime"' \
  -C panic=abort --crate-type staticlib -O \
  "$out/combined.rs" -o "$out/liblean_c_generated.a"
(cd examples && lean -c "$out/RuntimeHeapKernels.c" RuntimeHeapKernels.lean)
# Report original Lean C ABI and ownership branch before the differential
# comparison. These are diagnostic source facts, not assumptions about IR.
grep -nE 'l_RuntimeHeap_(first|make|observe|nest|payload|nestedFirst)[(]' "$out/RuntimeHeapKernels.c" | head -32
# Source-level ownership actions at the exact C ABI boundary.
sed -n '290,325p' "$out/RuntimeHeapKernels.c"
lean -c "$out/HeapDriver.c" runtime/lean-c/HeapDriver.lean
leanc -O2 -o "$out/lean-c-generated-heap" \
  "$out/RuntimeHeapKernels.c" "$out/HeapDriver.c" \
  runtime/lean-c/heap_oracle.c runtime/lean-c/abi.c \
  "$out/liblean_c_generated.a"
"$out/lean-c-generated-heap" | tee "$out/trace.txt"
grep -Fx 'reader-generated-lean-c-heap=PASS' "$out/trace.txt"
grep -Fx 'reader-generated-lean-c-nested-retain=PASS' "$out/trace.txt"
{
  echo 'status=PASS_ORIGINAL_LEAN_C_AND_READER_GENERATED_HEAP'
  echo "revision=$(git rev-parse HEAD)"
  echo "lean=$(lean --version)"
  echo "rust=$(rustc --version)"
  echo 'ir_declaration_roots=RuntimeHeap.make,RuntimeHeap.first,RuntimeHeap.observe,RuntimeHeap.nest,RuntimeHeap.payload,RuntimeHeap.nestedFirst'
  echo 'emitter=one_pinned_Reader_closure'
  echo 'runtime=actual_lean_C_heap_and_physical_RC'
  echo 'cases=100_small_Nat_pairs_plus_300_nested_pairs_and_stamps'
  echo 'heap_field_borrow=borrowed_pointer_no_source_inc'
  echo 'heap_field_retain=source_IR_inc_one_physical_Lean_C_credit'
  echo 'heap_ctor_field_transfer=source_credit_moved_without_increment'
  echo 'parent_release=retained_child_still_physically_owned'
  echo 'comparison=original_Lean_C_vs_same_emitter_Rust_C'
  echo 'physical_source_reference_counts=before_and_after_inc_dec'
  echo 'heap_child_scope=RuntimeHeap.Box.mk_of_RuntimeHeap.Pair.mk'
  echo 'other_heap_children_and_persistent=UNSUPPORTED'
  echo 'general_G1_and_G2=NOT_ESTABLISHED'
  sha256sum examples/RuntimeHeapKernels.lean \
    examples/RuntimeHeapFixture.lean runtime/lean-c/HeapDriver.lean \
    runtime/lean-c/generated_value.rs runtime/lean-c/heap_host.rs \
    runtime/lean-c/heap_oracle.c runtime/rust/immutable_value.rs \
    "$out/exact-emitter.rs" "$out/combined.rs" "$out/RuntimeHeapKernels.c" \
    "$out/HeapDriver.c" "$out/trace.txt"
} > "$out/receipt.txt"
cat "$out/receipt.txt"
