#!/usr/bin/env bash
# A SECOND diagnostic binary, built from the exact pinned Lean 4.34.1
# object.cpp with guarded trace hooks. The normal compiler + runtime and
# earlier uninstrumented witness checks remain untouched.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LEAN_PREFIX:?}"
export PATH="$LEAN_PREFIX/bin:$PATH"
export LEAN_PATH="$(pwd)/proofs:$(pwd)/examples:$(pwd):$LEAN_PREFIX/lib/lean"
export LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
test "$(lean --version)" = 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'
out="$(pwd)/artifacts/lean-c-generated-heap"
for file in RuntimeHeapKernels-traced.c RuntimeHeapDelKernels-traced.c SourceDelDriver.c abi-traced.c libsource_del_generated.a; do
  test -s "$out/$file"
done

# This checkout is immutable input to the patcher. No locally maintained
# reimplementation of lean_del_core/dec is accepted.
if [[ ! -d "$out/upstream-lean/.git" ]]; then
  git clone -q --depth 1 --filter=blob:none --sparse --branch v4.34.1 \
    https://github.com/leanprover/lean4.git "$out/upstream-lean"
  git -C "$out/upstream-lean" sparse-checkout set src/runtime src/include
fi
python3 scripts/instrument-pinned-worklist.py "$out/upstream-lean" \
  "$out/object-worklist-instrumented.cpp" | tee "$out/worklist-source-audit.txt"

# Compile the ORIGINAL full object.cpp translation unit with observation
# calls inserted at exact-checked sites. It exports lean_dec_ref_cold as
# the pinned runtime does. The linker resolves it from this object first.
leanc -O2 -std=c++17 -c -I"$out/upstream-lean/src" \
  -I"$out/upstream-lean/src/include" \
  "$out/object-worklist-instrumented.cpp" \
  -o "$out/object-worklist-instrumented.o"
nm -g "$out/object-worklist-instrumented.o" | grep -Eq ' [TW] lean_dec_ref_cold$'

leanc -O2 -o "$out/source-del-worklist-diagnostic" \
  "$out/object-worklist-instrumented.o" \
  "$out/RuntimeHeapKernels-traced.c" "$out/RuntimeHeapDelKernels-traced.c" \
  "$out/SourceDelDriver.c" runtime/lean-c/source_del_oracle.c \
  runtime/lean-c/source_shell_step_oracle.c \
  runtime/lean-c/source_release_oracle.c \
  runtime/lean-c/destructor_worklist_oracle.c \
  runtime/lean-c/source_del_event_trace.c \
  runtime/lean-c/worklist_internal_trace.c \
  "$out/abi-traced.c" "$out/libsource_del_generated.a"

LR_SOURCE_TRACE="$out/internal-shell-observations.tsv" \
LR_RELEASE_TRACE="$out/internal-release-observations.tsv" \
LR_DESTRUCTOR_WITNESSES="$out/internal-witnesses.tsv" \
LR_SOURCE_DEL_EVENTS="$out/internal-source-events.tsv" \
LR_WORKLIST_EVENTS="$out/internal-worklist-events.tsv" \
  "$out/source-del-worklist-diagnostic" \
  | tee "$out/internal-driver-output.txt"
grep -Fxq 'reader-generated-source-del-lean-c=PASS cases=720' \
  "$out/internal-driver-output.txt"
python3 scripts/check-internal-worklist.py \
  "$out/internal-worklist-events.tsv" --self-test \
  | tee "$out/internal-worklist-audit.txt"
grep -Fq 'worklist_internal_trace=PASS cases=8' "$out/internal-worklist-audit.txt"
grep -Fq 'worklist_internal_mutations=9/9_REFUSED' "$out/internal-worklist-audit.txt"
python3 scripts/check-destructor-witnesses.py "$out/internal-witnesses.tsv" \
  | tee "$out/internal-witness-audit.txt"
python3 - "$out/destructor-worklist-witnesses.tsv" "$out/internal-witnesses.tsv" <<'PY'
import csv, sys
def normalized(path):
    with open(path, newline="") as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
    return [(x["case"],x["phase"],x["index"],x["rc"]) for x in rows]
a,b=normalized(sys.argv[1]),normalized(sys.argv[2])
if a!=b: raise SystemExit("stock and instrumented C++ runtime physical witness divergence")
print("worklist_stock_vs_diagnostic_physical_effects=PASS rows="+str(len(a)))
PY
echo 'worklist_diagnostic_original_cpp=EXACT_UPSTREAM_BLOB_GUARDED'
echo 'worklist_internal_events=SAMPLED_EAGER_SINGLE_THREADED_CONSTRUCTORS'
echo 'worklist_production_runtime=UNCHANGED'
echo 'worklist_universal_cpp_correspondence=NOT_PROVED'
sha256sum scripts/instrument-pinned-worklist.py \
  scripts/check-internal-worklist.py \
  "$out/worklist-source-audit.txt" "$out/internal-worklist-events.tsv" \
  "$out/internal-worklist-audit.txt" "$out/internal-witnesses.tsv" \
  "$out/object-worklist-instrumented.cpp" \
  | tee "$out/internal-worklist-sha256.txt"
