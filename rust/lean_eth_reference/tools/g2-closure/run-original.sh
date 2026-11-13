#!/usr/bin/env bash
# Read-only, fail-closed inventory of the authentic pinned ETH QueryStream source.
# The caller must have *already* completed the original Lean/Mathlib import.
set -euo pipefail

if (( $# != 3 )); then
  echo "usage: run-original.sh ORIGINAL_SOURCE_CHECKOUT PINNED_LAKE_ROOT OUTPUT_DIR" >&2
  exit 2
fi

original="$(realpath "$1")"
lake_root="$(realpath "$2")"
out="$(realpath -m "$3")"
tool="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source_sha=4eaee87548250b2682affda7d05d947c05554bae
mathlib_sha=d13f23b723b8a846827a245b89c10fc7d3f11612
query_blob=c2fb29983bb33229d5cf60729cd3d1e37b9b00ca
query_path=lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamProgram.lean

fail() { echo "original closure inventory refused: $*" >&2; exit 2; }

[[ "$(git -C "$original" rev-parse HEAD)" == "$source_sha" ]] || fail "source commit mismatch"
[[ -z "$(git -C "$original" status --porcelain --untracked-files=no)" ]] || fail "source checkout changed"
[[ "$(git -C "$original" rev-parse "HEAD:$query_path")" == "$query_blob" ]] || fail "QueryStream source blob mismatch"
[[ "$(cat "$lake_root/lean-toolchain")" == "leanprover/lean4:v4.34.1" ]] || fail "Lean toolchain mismatch"
[[ "$(git -C "$lake_root/.lake/packages/mathlib" rev-parse HEAD)" == "$mathlib_sha" ]] || fail "Mathlib revision mismatch"
[[ -L "$lake_root/OAI" ]] || fail "original source module symlink missing"
[[ "$(realpath "$lake_root/OAI")" == "$(realpath "$original/lean/OAI")" ]] || fail "Lake OAI link points to wrong source"

# Never overwrite an old inventory/receipt and never turn an incomplete scan into success.
mkdir -p "$out"
[[ ! -e "$out/original-query-inventory.json" && ! -e "$out/original-query-inventory.receipt.json" ]] ||
  fail "existing output; choose a fresh directory"
tmp="$(mktemp -d "$out/.g2-inventory.XXXXXXXX")"
trap 'rm -rf "$tmp"' EXIT
export LEAN_PATH="$tmp${LEAN_PATH:+:$LEAN_PATH}"

(
  cd "$lake_root"
  lake env lean -o "$tmp/G2Inventory.olean" "$tool/G2Inventory.lean"
  # OriginalQuery imports the actual original .olean module. No synthetic fallback.
  timeout 1800s lake env lean "$tool/OriginalQuery.lean" > "$tmp/inventory.json"
) || fail "original module import or inventory refused; no acceptance artifact published"

# Exact one-object output, complete bounded scan, and explicitly unproved semantics.
jq -e -s '
  length == 1
  and .[0].format == "eth-original-closure-inventory-v1"
  and .[0].root == "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.program"
  and .[0].status == "syntactic-closure-observed"
  and .[0].complete_syntactic_body_walk == true
  and .[0].eth_ready == false
  and .[0].computational_relevance_verified == false
  and .[0].lean_rust_semantic_refinement == "not-established"
  and .[0].physical_bitprogram_refinement == "not-established"
' "$tmp/inventory.json" >/dev/null || fail "incomplete or invalid source inventory"

source_hash="$(git -C "$original" rev-parse "HEAD:$query_path")"
inventory_hash="$(sha256sum "$tmp/inventory.json" | cut -d' ' -f1)"
lean_version="$(cd "$lake_root" && lake env lean --version)"
jq -n \
  --arg source_commit "$source_sha" \
  --arg source_blob "$source_hash" \
  --arg mathlib_commit "$mathlib_sha" \
  --arg toolchain "leanprover/lean4:v4.34.1" \
  --arg lean_version "$lean_version" \
  --arg inventory_sha256 "$inventory_hash" \
  '{
    format: "eth-original-inventory-receipt-v1",
    source_commit: $source_commit,
    query_source_blob: $source_blob,
    mathlib_commit: $mathlib_commit,
    lean_toolchain: $toolchain,
    observed_lean_version: $lean_version,
    inventory_sha256: $inventory_sha256,
    status: "syntactic-closure-only",
    code_generated: false,
    lean_rust_semantics: "not-established",
    physical_refinement: "not-established",
    eth_ready: false
  }' > "$tmp/receipt.json"
mv "$tmp/inventory.json" "$out/original-query-inventory.json"
mv "$tmp/receipt.json" "$out/original-query-inventory.receipt.json"
echo "Original source inventory recorded, not executable or ETH-ready."
