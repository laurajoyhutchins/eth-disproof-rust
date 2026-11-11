#!/usr/bin/env bash
# Execute ORIGINAL imported Lean definitions and Rust separately, then compare.
# This suite refuses to pass if the pinned Lean/Mathlib source or runtime is missing.
set -euo pipefail

CRATE="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
REPOSITORY="$(cd -- "$CRATE/../.." && pwd)"
UPSTREAM=""
OUT="$REPOSITORY/target/lean-differential"
SUITE=full
SOURCE_SHA=4eaee87548250b2682affda7d05d947c05554bae
MATHLIB_SHA=d13f23b723b8a846827a245b89c10fc7d3f11612

usage() {
  cat <<'HELP'
Usage: scripts/verify-lean-differential.sh --lean-repo /path/to/openai/math [--suite full|all|high|tuple|layout|nodes|query] [--output-dir PATH]

The OpenAI checkout must be at 4eaee87548250b2682affda7d05d947c05554bae,
with a complete Lean 4.34.1 and pinned Mathlib cache. No fake Lean source or
previously recorded trace is accepted. Each suite is independently rerunnable.
HELP
}
while (( $# )); do
  case "$1" in
    --lean-repo) UPSTREAM="${2:?requires path}"; shift 2 ;;
    --suite) SUITE="${2:?requires suite}"; shift 2 ;;
    --output-dir) OUT="${2:?requires directory}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) usage >&2; echo "Unexpected argument: $1" >&2; exit 2 ;;
  esac
done
[[ -n "$UPSTREAM" ]] || { usage >&2; echo 'Missing --lean-repo' >&2; exit 2; }
for tool in git python3 cargo rustc lake; do
  command -v "$tool" >/dev/null || { echo "BLOCKED: $tool unavailable" >&2; exit 3; }
done
UPSTREAM="$(realpath -- "$UPSTREAM")"
OUT="$(realpath -m -- "$OUT")"
mkdir -p -- "$OUT"
# A failed rerun must never leave a stale success receipt.
rm -f -- "$OUT/receipt.json" "$OUT/"*.pass

[[ -f "$UPSTREAM/lean/lakefile.lean" ]] || {
  echo 'BLOCKED: no pinned upstream lean/lakefile.lean checkout' >&2; exit 3;
}
observed="$(git -C "$UPSTREAM" rev-parse HEAD)"
[[ "$observed" == "$SOURCE_SHA" ]] || {
  echo "BLOCKED: wrong OpenAI source commit: $observed" >&2; exit 3;
}
if [[ -n "$(git -C "$UPSTREAM" status --porcelain --untracked-files=all -- lean/OAI/Algorithms/SubexponentialSAT)" ]]; then
  echo 'BLOCKED: OpenAI source tree has uncommitted additions/modifications' >&2; exit 3
fi
MATHLIB="$UPSTREAM/lean/.lake/packages/mathlib"
[[ -d "$MATHLIB" ]] || { echo 'BLOCKED: Mathlib checkout missing' >&2; exit 3; }
mathlib_head="$(git -C "$MATHLIB" rev-parse HEAD)"
[[ "$mathlib_head" == "$MATHLIB_SHA" ]] || {
  echo "BLOCKED: wrong Mathlib source commit: $mathlib_head" >&2; exit 3;
}
lean_version="$(cd "$UPSTREAM/lean" && env -u LEAN_PATH -u LEAN_SRC_PATH lake env lean --version)"
[[ "$lean_version" == "Lean (version 4.34.1,"* ]] || {
  echo "BLOCKED: expected Lean 4.34.1, got $lean_version" >&2; exit 3;
}
rust_head="$(git -C "$REPOSITORY" rev-parse HEAD)"
if [[ -n "$(git -C "$REPOSITORY" status --porcelain --untracked-files=all -- rust/lean_eth_reference/src rust/lean_eth_reference/reference rust/lean_eth_reference/scripts)" ]]; then
  echo "BLOCKED: Rust checkout contains uncommitted source or observer changes" >&2; exit 3
fi
rust_version="$(rustc --version)"
[[ "$rust_version" == rustc\ 1.99.1\ * ]] || {
  echo "BLOCKED: expected rustc 1.99.1, got $rust_version" >&2; exit 3;
}
# One honest Mathlib import, not a compiler-version smoke test alone.
printf 'import Mathlib\n#eval 40 + 2\n' > "$OUT/import-mathlib.lean"
if ! (cd "$UPSTREAM/lean" && env -u LEAN_PATH -u LEAN_SRC_PATH lake env lean "$OUT/import-mathlib.lean") >"$OUT/import-mathlib.stdout" 2>"$OUT/import-mathlib.stderr"; then
  echo "BLOCKED: authentic import Mathlib failed. Inspect $OUT/import-mathlib.stderr" >&2
  exit 4
fi
grep -qx '42' "$OUT/import-mathlib.stdout" || {
  echo 'BLOCKED: Mathlib import smoke produced unexpected output' >&2; exit 4;
}

case "$SUITE" in
  full) suites=(full) ;;
  high) suites=(high) ;;
  tuple) suites=(tuple) ;;
  layout) suites=(layout) ;;
  nodes) suites=(nodes) ;;
  query) suites=(query) ;;
  all) suites=(full high tuple layout nodes query) ;;
  *) echo "Invalid suite: $SUITE" >&2; exit 2 ;;
esac

# No fixtures from a previous run can substitute for either execution.
(cd "$CRATE" && cargo build --locked --offline --bins)
for part in "${suites[@]}"; do
  case "$part" in
    full) lean=lean_full_machine_trace.lean; bin=lean-full-machine-trace; compare=compare-full-machine-trace.py; modules=(SqrtLog.HighIncidenceProgramBranches) ;;
    high) lean=lean_native_high_trace.lean; bin=native-high-trace; modules=(SqrtLog.HighIncidenceProgramBranches SqrtLogSpace.HighCountSeed) ;;
    tuple) lean=lean_native_tuple_trace.lean; bin=native-tuple-trace; modules=(ExecCNFTupleOdometer ExecCNFTupleEnumeration) ;;
    layout) lean=lean_native_layout_pair_trace.lean; bin=native-layout-pair-trace; modules=(SqrtLogSpace.NativeLayoutLoad SqrtLogSpace.PairNativeSetup) ;;
    nodes) lean=lean_native_nodes_trace.lean; bin=native-nodes-trace; modules=(SqrtLogSpace.QueryAssembler SqrtLogSpace.QueryNodeFinish) ;;
    query) lean=lean_native_query_prefix_trace.lean; bin=native-query-prefix-trace; modules=(SqrtLogSpace.HighQueryAdapter) ;;
  esac
  # Rebuild imported target modules from the pinned source so stale OAI .olean
  # files from a different revision cannot masquerade as upstream code.
  for module in "${modules[@]}"; do
    (cd "$UPSTREAM/lean" && env -u LEAN_PATH -u LEAN_SRC_PATH lake build "OAI.Algorithms.SubexponentialSAT.$module") > "$OUT/$part.build.stdout" 2> "$OUT/$part.build.stderr"
  done
  # Delete stale files so failed commands cannot leave an apparently passing pair.
  rm -f -- "$OUT/$part.lean.trace" "$OUT/$part.rust.trace" "$OUT/$part.pass"
  (cd "$UPSTREAM/lean" && env -u LEAN_PATH -u LEAN_SRC_PATH lake env lean --run "$CRATE/reference/$lean") > "$OUT/$part.lean.trace"
  "$REPOSITORY/target/debug/$bin" > "$OUT/$part.rust.trace"
  if [[ "$part" == full ]]; then
    # The full-state Python parser remains shared with the resource profiler.
    python3 "$CRATE/scripts/$compare" --lean "$OUT/$part.lean.trace" --rust "$OUT/$part.rust.trace"
  else
    # One Rust validator for all five source-specific snapshot schemas.
    "$REPOSITORY/target/debug/compare-traces" --suite "$part" \
      --lean "$OUT/$part.lean.trace" --rust "$OUT/$part.rust.trace"
  fi
  if [[ "$part" == full ]]; then
    # Independent state comparison must pass before extra profiling.
    rm -f -- "$OUT/full.rust.ops.csv" "$OUT/full.profile.json"
    "$REPOSITORY/target/debug/profile-full-machine" > "$OUT/full.rust.ops.csv"
    python3 "$CRATE/scripts/profile-full-machine-traces.py" \
      --lean "$OUT/full.lean.trace" --rust "$OUT/full.rust.trace" \
      --rust-metrics "$OUT/full.rust.ops.csv" --output "$OUT/full.profile.json"
  fi
  printf '%s\n' "source=$SOURCE_SHA" "mathlib=$MATHLIB_SHA" "lean=$lean_version" "rust=$rust_version" > "$OUT/$part.pass"
done
# Write receipt ONLY after every fresh source execution and comparison succeeded.
python3 - "$OUT" "$SOURCE_SHA" "$MATHLIB_SHA" "$lean_version" "$rust_version" "$rust_head" "${suites[@]}" <<'PY'
import hashlib, json, pathlib, sys
out = pathlib.Path(sys.argv[1]); src, math, lean, rust, rust_head = sys.argv[2:7]; suites = sys.argv[7:]
entries = {}
for suite in suites:
    paths = (out / f'{suite}.lean.trace', out / f'{suite}.rust.trace')
    entries[suite] = {
        name: {'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size}
        for name, path in zip(('lean', 'rust'), paths)
    }
    if suite == 'full':
        for name, path in (('rust_opcode_profile', out / 'full.rust.ops.csv'),
                           ('state_resource_profile', out / 'full.profile.json')):
            entries[suite][name] = {
                'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'bytes': path.stat().st_size,
            }
receipt = {'status': 'PASS', 'provenance': {'openai_math_commit': src, 'mathlib_commit': math, 'lean': lean, 'rust': rust, 'rust_commit': rust_head}, 'suites': entries}
(out / 'receipt.json').write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
print(f'PASS: {len(suites)} genuine imported-Lean differential suites. Receipt: {out / "receipt.json"}')
PY
