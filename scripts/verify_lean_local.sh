#!/usr/bin/env bash
# Run pinned OpenAI Lean with a reusable local Lake build, not an ephemeral CI VM.
set -Eeuo pipefail
if [[ "$#" -eq 1 && "$1" == "--help" ]]; then
  cat <<'HELP'
LEAN_UPSTREAM=/path/to/openai-math LEAN_CACHE_ROOT=/persistent/lean \
  bash scripts/verify_lean_local.sh
Requires Lean 4.34.1, pinned upstream source and Mathlib, and matching Lake.
LEAN_SKIP_CACHE_GET=1: use already-restored offline Mathlib cache.
LEAN_BUILD_JOBS=2: limit concurrent compilation jobs.
LEAN_TRACE_KIND=semantic (default) or primitive (when driver is present).
No GitHub Actions runner is needed.
HELP
  exit 0
fi
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="$(printenv PYTHON_BIN || echo python3)"
LEAN="$(printenv LEAN_BIN || echo lean)"
LAKE="$(printenv LAKE_BIN || echo lake)"
for cmd in git "$PY" "$LEAN" "$LAKE"; do
  command -v "$cmd" >/dev/null 2>&1 || {
    echo "Missing $cmd. Restore exact Lean 4.34.1 and matching Lake." >&2
    exit 2
  }
done
UPSTREAM="$(printenv LEAN_UPSTREAM || true)"
if [[ -z "$UPSTREAM" || ! -d "$UPSTREAM/lean/OAI/Algorithms/SubexponentialSAT" ]]; then
  echo "LEAN_UPSTREAM must point to a local openai/math source checkout." >&2
  exit 2
fi
UPSTREAM="$(cd "$UPSTREAM" && pwd)"
read -r EXPECTED_SHA MATHLIB_SHA < <("$PY" - "$ROOT/reference/lean_eth_source.json" <<'PY'
import json
import sys
with open(sys.argv[1], encoding="utf-8") as inp:
    pin = json.load(inp)
assert pin["repository"] == "openai/math"
assert pin["toolchain"] == "leanprover/lean4:v4.34.1"
print(pin["commit"], pin["mathlib_commit"])
PY
)
SOURCE_SHA="$(git -C "$UPSTREAM" rev-parse HEAD)"
if [[ "$SOURCE_SHA" != "$EXPECTED_SHA" ]]; then
  echo "Wrong OpenAI source HEAD: $SOURCE_SHA; expected $EXPECTED_SHA" >&2
  exit 2
fi
if [[ "$(tr -d '\r\n' < "$UPSTREAM/lean/lean-toolchain")" != "leanprover/lean4:v4.34.1" ]] ||
   ! grep -Fq "$MATHLIB_SHA" "$UPSTREAM/lean/lake-manifest.json"; then
  echo "Wrong upstream Lean/Mathlib pin." >&2
  exit 2
fi
VERSION="$("$LEAN" --version)"
LAKE_VERSION="$("$LAKE" --version)"
if [[ "$VERSION" != *"Lean (version 4.34.1,"* || "$LAKE_VERSION" != *"Lean version 4.34.1"* ]]; then
  echo "Wrong compiler/toolchain: $VERSION / $LAKE_VERSION" >&2
  exit 2
fi

CACHE_ROOT="$(printenv LEAN_CACHE_ROOT || true)"
if [[ -z "$CACHE_ROOT" ]]; then CACHE_ROOT="$HOME/.cache/nonexp-sudoku/lean"; fi
KEY="linux-$(uname -m)-lean-v4.34.1-$EXPECTED_SHA-$MATHLIB_SHA"
OVERLAY="$CACHE_ROOT/$KEY"
OUT="$CACHE_ROOT/evidence/$KEY"
mkdir -p "$OVERLAY" "$OUT"
cat > "$OVERLAY/lakefile.lean" <<EOF
import Lake
open Lake DSL
package OAI where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "$MATHLIB_SHA"
@[default_target] lean_lib OAI
EOF
cp "$UPSTREAM/lean/lean-toolchain" "$OVERLAY/lean-toolchain"
if [[ ! -e "$OVERLAY/OAI" && ! -L "$OVERLAY/OAI" ]]; then
  ln -s "$UPSTREAM/lean/OAI" "$OVERLAY/OAI"
fi
if [[ ! -L "$OVERLAY/OAI" || "$(readlink "$OVERLAY/OAI")" != "$UPSTREAM/lean/OAI" ]]; then
  echo "Stale source symlink in persistent cache; refusing." >&2
  exit 2
fi

cd "$OVERLAY"
if [[ ! -f "$OVERLAY/lake-manifest.json" ]]; then "$LAKE" update; fi
if [[ ! -d "$OVERLAY/.lake/packages/mathlib" ]]; then
  echo "Missing pinned Mathlib checkout. Restore cache or initialize online." >&2
  exit 2
fi
MATHLIB_HEAD="$(git -C "$OVERLAY/.lake/packages/mathlib" rev-parse HEAD)"
if [[ "$MATHLIB_HEAD" != "$MATHLIB_SHA" ]]; then
  echo "Wrong Mathlib revision: $MATHLIB_HEAD" >&2
  exit 2
fi
if [[ "$(printenv LEAN_SKIP_CACHE_GET || true)" != "1" ]]; then
  "$LAKE" exe cache get
fi
JOBS="$(printenv LEAN_BUILD_JOBS || echo 2)"
if [[ ! "$JOBS" =~ ^[1-9][0-9]*$ ]]; then
  echo "LEAN_BUILD_JOBS must be a positive integer." >&2
  exit 2
fi
# Semantic counting DFS is already source-executed and verified upstream.
# Primitive-mode execution is a separate, still-unverified contract.
MODE="$(printenv LEAN_TRACE_KIND || echo semantic)"
OUT="$OUT/$MODE"
mkdir -p "$OUT"
case "$MODE" in
  semantic)
    DRIVER="$ROOT/reference/lean_native_trace.lean"
    COMPARATOR=scripts.compare_lean_trace
    "$LAKE" build -j "$JOBS" \
      OAI.Algorithms.SubexponentialSAT.Encoding \
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointSparsify \
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram \
      2>&1 | tee "$OUT/build.log"
    ;;
  primitive)
    DRIVER="$ROOT/reference/lean_primitive_trace.lean"
    COMPARATOR=scripts.compare_lean_primitive
    if [[ ! -f "$DRIVER" ]]; then
      echo "Primitive trace driver not checked out; refusing fallback." >&2
      exit 2
    fi
    "$LAKE" build -j "$JOBS" \
      OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram \
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal \
      2>&1 | tee "$OUT/build.log"
    ;;
  *)
    echo "Unsupported LEAN_TRACE_KIND: $MODE" >&2
    exit 2
    ;;
esac
"$LAKE" env "$LEAN" --run "$DRIVER" \
  > "$OUT/native-trace.txt" 2> "$OUT/native-stderr.txt"
cd "$ROOT"
PYTHONPATH="$ROOT/src:$ROOT" "$PY" -m "$COMPARATOR" \
  --input "$OUT/native-trace.txt" | tee "$OUT/comparison.txt"
{
  echo "$VERSION"
  echo "mode=$MODE source=$SOURCE_SHA mathlib=$MATHLIB_HEAD"
  sha256sum "$OUT/native-trace.txt"
} > "$OUT/evidence.txt"
echo "PASS: $MODE evidence at $OUT"
