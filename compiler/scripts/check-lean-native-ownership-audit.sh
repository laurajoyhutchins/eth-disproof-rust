#!/usr/bin/env bash
# Pinned, independent final-IR audit + unchanged canonical physical runtime oracle.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LEAN_PREFIX:?Set LEAN_PREFIX to pinned Lean 4.34.1}"
export PATH="$LEAN_PREFIX/bin:$PATH"
export LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export LEAN_PATH="$PWD:$PWD/examples:$PWD/proofs:$LEAN_PREFIX/lib/lean"
test "$(cat lean-toolchain)" = "leanprover/lean4:v4.34.1"
test "$(lean --version)" = 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'
test "$(rustc --version)" = 'rustc 1.99.1 (58cf8f9c3 2026-10-13)'
out=artifacts/lean-native-ownership
test ! -e "$out"
mkdir -p artifacts
lean -o LeanNativeOwnershipAudit.olean LeanNativeOwnershipAudit.lean
lean -o examples/RuntimeHeapKernels.olean examples/RuntimeHeapKernels.lean
lean -o examples/RuntimeHeapDelKernels.olean examples/RuntimeHeapDelKernels.lean
lean examples/RuntimeHeapDelIRProbe.lean > artifacts/lean-native-ownership-ir-probe.log
/usr/bin/time -f 'native_ir_audit_elapsed_s=%e peak_kb=%M' \
  -o artifacts/lean-native-ownership-audit.time \
  lean examples/LeanNativeOwnershipFixture.lean \
  > artifacts/lean-native-ownership-audit.log
python3 scripts/check-lean-native-ownership-manifest.py \
  "$out/events.tsv" "$out/counts.tsv" artifacts/source-del-final-ir.tsv --self-test \
  | tee artifacts/lean-native-ownership-audit-status.txt

# Preserve and regenerate the manifest to test the independent Lean emitter.
cp -a "$out" artifacts/lean-native-ownership-first
rm -rf "$out"
lean examples/LeanNativeOwnershipFixture.lean > artifacts/lean-native-ownership-second.log
cmp artifacts/lean-native-ownership-first/events.tsv "$out/events.tsv"
cmp artifacts/lean-native-ownership-first/counts.tsv "$out/counts.tsv"

# A native-IR ownership audit is *not* executable source-admission.
# The scalar-only Lean-native Rust emitter must refuse the original
# heap declaration rather than fake a runtime or emit a partial package.
lean -o LeanNativeRustIR.olean LeanNativeRustIR.lean
cat > artifacts/LeanNativeOwnershipRefusal.lean <<'LEAN'
import LeanNativeRustIR
import RuntimeHeapDelKernels
#lean_native_ir_package [RuntimeHeapDel.rebuildOrExtractByPayload]
  to "artifacts/lean-native-refused-heap"
LEAN
if lean artifacts/LeanNativeOwnershipRefusal.lean \
    > artifacts/lean-native-ownership-refusal.log 2>&1; then
  echo "Lean-native scalar emitter incorrectly accepted heap ownership" >&2
  exit 2
fi
grep -Fq 'Lean-native emitter refused:' artifacts/lean-native-ownership-refusal.log
test ! -e artifacts/lean-native-refused-heap

# Reuse exact original Lean C / unchanged Reader-generated Rust physical oracle.
cargo build --locked --offline --release
export NATIVE_LIB="$PWD/target/release/liblean_rust_native_backend.so"
lean -o NativeRust.olean NativeRust.lean
bash runtime/lean-c/check-generated-heap.sh \
  > artifacts/lean-native-ownership-physical.log 2>&1

# The canonical physical run independently checks eight source-visible event
# branches and the source-origin final-state comparisons.
grep -Fq 'source_del_original_C_vs_exact_Reader_event_parity=PASS cases=8 lanes=16' \
  artifacts/lean-c-generated-heap/source-del-events-audit.txt
python3 scripts/check-lean-native-ownership-manifest.py \
  "$out/events.tsv" "$out/counts.tsv" artifacts/source-del-final-ir.tsv \
  --reader-source artifacts/lean-c-generated-heap/source-del-exact-reader.rs \
  --self-test | tee artifacts/lean-native-ownership-physical-cross-check.txt

{
  printf 'commit='; git rev-parse HEAD
  lean --version
  rustc --version
  sha256sum examples/RuntimeHeapKernels.lean examples/RuntimeHeapDelKernels.lean \
    LeanNativeOwnershipAudit.lean \
    backend/src/reader/lifetime.rs \
    artifacts/source-del-final-ir.txt \
    "$out/events.tsv" "$out/counts.tsv" \
    artifacts/lean-c-generated-heap/source-del-events.tsv
  cat artifacts/lean-native-ownership-audit.time
  cat artifacts/lean-native-ownership-physical-cross-check.txt
  echo 'scope=source_IR_structural_inventory_plus_reused_canonical_physical_oracle'
  echo 'lean_native_ownership_codegen=NOT_IMPLEMENTED; SCALAR_EMITTER_REFUSES'
  echo 'full_ownership_refinement=NOT_PROVED'
} | tee artifacts/lean-native-ownership-receipt.txt
