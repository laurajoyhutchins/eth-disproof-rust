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
# Kernel-check the abstract source-credit / physical-count simulation
# before compiling expensive generated Rust and Lean C integrations.
lean proofs/ReaderShellSimulation.lean | tee "$out/source-shell-simulation-lean.txt"
grep -Fq "'ReaderShellSimulation.trace_simulation' does not depend on any axioms" \
  "$out/source-shell-simulation-lean.txt"
grep -Fq "'ReaderShellSimulation.recursive_delete_is_not_shell_delete' does not depend on any axioms" \
  "$out/source-shell-simulation-lean.txt"
rm -rf examples/lean-c-heap-package
lean -o examples/RuntimeHeapKernels.olean examples/RuntimeHeapKernels.lean
# Examine the compiler's actual final IR for source-derived reset/reuse
# candidates. The probe records negative findings instead of inventing
# a final IR del or asserting runtime execution.
lean -o examples/RuntimeHeapDelKernels.olean examples/RuntimeHeapDelKernels.lean
lean examples/RuntimeHeapDelIRProbe.lean
test -s artifacts/source-del-final-ir.tsv
test -s artifacts/source-del-final-ir.txt
test -s artifacts/source-del-final-ir-status.txt
grep -Fx 'stage=FINAL_IR_DISCOVERY_ONLY' artifacts/source-del-final-ir-status.txt
cat artifacts/source-del-final-ir.tsv
cat artifacts/source-del-final-ir-status.txt
# Probe the canonical Reader closure of the positive source. A refusal is
# evidence of the next missing feature, not a successful source-del execution.
# Atomic publication must leave no package after a failed compilation.
rm -rf examples/lean-c-del-package
if lean --load-dynlib="$NATIVE_LIB" examples/RuntimeHeapDelEmitFixture.lean \
    > "$out/source-del-emit.log" 2>&1; then
  del_rs=examples/lean-c-del-package/src/lib.rs
  test -s "$del_rs"
  grep -Fq 'Generated directly from Lean IR declaration: RuntimeHeapDel.rebuildOrExtractByPayload' "$del_rs"
  grep -Fq '.source_del();' "$del_rs" || {
    echo 'Final source del missing from canonical Reader output' >&2
    exit 2
  }
  cp "$del_rs" "$out/source-del-exact-reader.rs"
  # Type-check the exact, unedited emitted function against the real
  # Lean C-backed adapter. This is NOT an execution or physical parity gate.
  rustc --edition=2021 --cfg 'feature="lean-c-runtime"' \
    -C panic=abort --crate-type lib --emit=metadata \
    "$out/source-del-exact-reader.rs" -o "$out/source-del-exact-reader.rmeta"
  echo 'source_del_reader=TYPED_LEAN_C_NOT_EXECUTED' > "$out/source-del-reader-status.txt"
else
  grep -Fq 'Rust native backend refused' "$out/source-del-emit.log" || {
    echo 'Source del Reader probe failed before a recorded backend refusal' >&2
    cat "$out/source-del-emit.log" >&2
    exit 2
  }
  test ! -e examples/lean-c-del-package || {
    echo 'Reader published a partial package after refusal' >&2
    exit 2
  }
  echo 'source_del_reader=REFUSED' > "$out/source-del-reader-status.txt"
  cat "$out/source-del-emit.log" >&2
  echo 'Canonical Reader failed to emit the verified original source del' >&2
  exit 2
fi
cat "$out/source-del-reader-status.txt"
cat "$out/source-del-emit.log"
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
# Ground the host wrapper's parameter mode in the unchanged original C
# compiler output. The unboxed function must borrow the parent; the boxed
# entry point applies the caller's source-defined parent decrement.
python3 - "$out/RuntimeHeapKernels.c" <<'PY'
from pathlib import Path
import re
import sys
s = Path(sys.argv[1]).read_text()
def function_body(name):
    # Match an actual generated C definition, not a forward declaration.
    pattern = rf"LEAN_EXPORT\s+lean_object\*\s+{re.escape(name)}\([^;{{}}]*\)\s*\{{"
    match = re.search(pattern, s)
    if match is None:
        raise SystemExit(f"original Lean C definition missing: {name}")
    following = s.find("LEAN_EXPORT", match.end())
    return s[match.start():following if following >= 0 else len(s)]
body = function_body("l_RuntimeHeap_payload")
boxed_body = function_body("l_RuntimeHeap_payload___boxed")
if "lean_ctor_get(" not in body or "lean_inc(" not in body:
    raise SystemExit("original Lean C payload does not borrow/retain child")
if "lean_dec(" in body or "lean_dec(" not in boxed_body:
    raise SystemExit("original Lean C unboxed/boxed parent ownership ABI changed")
print("original_lean_payload_abi=BORROWED_PARENT_OWNED_CHILD")
PY
lean -c "$out/HeapDriver.c" runtime/lean-c/HeapDriver.lean
leanc -O2 -o "$out/lean-c-generated-heap" \
  "$out/RuntimeHeapKernels.c" "$out/HeapDriver.c" \
  runtime/lean-c/heap_oracle.c runtime/lean-c/abi.c \
  "$out/liblean_c_generated.a"
"$out/lean-c-generated-heap" | tee "$out/trace.txt"
grep -Fx 'reader-generated-lean-c-heap=PASS' "$out/trace.txt"
grep -Fx 'reader-generated-lean-c-nested-retain=PASS' "$out/trace.txt"
grep -Fx 'lean-c-shell-only-del-transfer=PASS' "$out/trace.txt"
# A distinct executable links the original C-compiled source function and
# the exact Reader-generated Rust function through the same Lean C runtime.
# Do not modify either function, or replace a source-del with host code.
test -s "$out/source-del-exact-reader.rs"
cat "$out/source-del-exact-reader.rs" runtime/lean-c/source_del_host.rs \
  > "$out/source-del-combined.rs"
rustc --edition=2021 --cfg 'feature="lean-c-runtime"' \
  -C panic=abort --crate-type staticlib -O \
  "$out/source-del-combined.rs" -o "$out/libsource_del_generated.a"
(cd examples && lean -c "$out/RuntimeHeapDelKernels.c" RuntimeHeapDelKernels.lean)
grep -Fq 'lean_del_object(' "$out/RuntimeHeapDelKernels.c" || {
  echo 'Original Lean C source lacks shell-only del' >&2
  exit 2
}
lean -c "$out/SourceDelDriver.c" runtime/lean-c/SourceDelDriver.lean
leanc -O2 -o "$out/source-del-execute" \
  "$out/RuntimeHeapKernels.c" "$out/RuntimeHeapDelKernels.c" \
  "$out/SourceDelDriver.c" runtime/lean-c/source_del_oracle.c \
  runtime/lean-c/abi.c "$out/libsource_del_generated.a"
"$out/source-del-execute" | tee "$out/source-del-trace.txt"
grep -Fx 'reader-generated-source-del-lean-c=PASS cases=720' "$out/source-del-trace.txt"
echo 'source_del_original_lean_c_vs_exact_reader=PASS_BOUNDED_720' \
  > "$out/source-del-execution-status.txt"
echo 'source_del_reader=EXECUTED_BOUNDED_720' > "$out/source-del-reader-status.txt"
{
  echo 'status=PASS_ORIGINAL_LEAN_C_AND_READER_GENERATED_HEAP'
  echo 'source_shell_abstract_trace_simulation=LEAN_KERNEL_VERIFIED_RESTRICTED_MACHINE'
  echo 'source_shell_original_lean_c_refinement=NOT_ESTABLISHED'
  sha256sum proofs/ReaderShellSimulation.lean "$out/source-shell-simulation-lean.txt"
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
  echo 'runtime_shell_del=PINNED_LEAN_C_FFI_PRIMITIVE_MATCHED'
  echo 'shell_only_child_transfer=ONE_CREDIT_NO_INC'
  echo 'shell_del_no_projection=REFUSED'
  echo 'shell_del_shared_parent=REFUSED'
  echo 'emitted_ir_source_del=PASS_BOUNDED_720_PHYSICAL_FINAL_STATES'
  echo 'source_del_full_traces_and_general_equivalence=NOT_ESTABLISHED'
  cat "$out/source-del-execution-status.txt"
  sha256sum runtime/lean-c/source_del_host.rs runtime/lean-c/source_del_oracle.c \
    runtime/lean-c/SourceDelDriver.lean "$out/source-del-combined.rs" \
    "$out/RuntimeHeapDelKernels.c" "$out/SourceDelDriver.c" \
    "$out/source-del-trace.txt"
  cat "$out/source-del-reader-status.txt"
  sha256sum examples/RuntimeHeapDelEmitFixture.lean "$out/source-del-emit.log" \
    "$out/source-del-reader-status.txt"
  cat artifacts/source-del-final-ir-status.txt
  sha256sum examples/RuntimeHeapDelKernels.lean examples/RuntimeHeapDelIRProbe.lean \
    artifacts/source-del-final-ir.tsv artifacts/source-del-final-ir.txt \
    artifacts/source-del-final-ir-status.txt
  echo 'join_transfer=NOT_YET_ESTABLISHED'
  echo 'unboxed_payload_argument=BORROWED'
  echo 'boxed_payload_wrapper=RELEASES_PARENT'
  echo 'host_wrapper=FROM_BORROWED_RAW_NO_INVENTED_DEC'
  echo 'comparison=original_Lean_C_vs_same_emitter_Rust_C'
  echo 'physical_source_reference_counts=before_and_after_inc_dec'
  echo 'heap_child_scope=RuntimeHeap.Box.mk_of_RuntimeHeap.Pair.mk'
  echo 'other_heap_children_and_persistent=UNSUPPORTED'
  echo 'general_G1_and_G2=NOT_ESTABLISHED'
  sha256sum examples/RuntimeHeapKernels.lean \
    examples/RuntimeHeapFixture.lean runtime/lean-c/HeapDriver.lean \
    runtime/lean-c/generated_value.rs runtime/lean-c/heap_host.rs \
    runtime/lean-c/heap_oracle.c runtime/lean-c/abi.c \
    runtime/rust/immutable_value.rs \
    "$out/exact-emitter.rs" "$out/combined.rs" "$out/RuntimeHeapKernels.c" \
    "$out/HeapDriver.c" "$out/trace.txt"
} > "$out/receipt.txt"
cat "$out/receipt.txt"
