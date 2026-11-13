#!/usr/bin/env bash
# Acceptance tests for atomic, no-overwrite provenance bundles.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p artifacts
sandbox="$(mktemp -d "$(pwd)/artifacts/bundle-test.XXXXXXXX")"
trap 'rm -rf -- "$sandbox"' EXIT
out="$sandbox/accepted"

bash scripts/compile-bundle.sh PropertyDef Property.hop \
  examples/PropertyDef.lean "$out" property_hop \
  > "$sandbox/compile-success.log"
test -s "$out/generated.rs"
test -s "$out/libgenerated.rlib"
test -s "$out/closure.txt"
grep -Fxq 'Property.hop' "$out/closure.txt"
grep -Fxq 'status=GENERATED_COMPILED_UNVERIFIED' "$out/receipt.txt"
grep -Fxq 'semantic_verification=NOT_PERFORMED' "$out/receipt.txt"
grep -Fq 'source_lean_sha256=' "$out/receipt.txt"
grep -Fq 'compiled_olean_sha256=' "$out/receipt.txt"
grep -Fq 'native_shared_library_sha256=' "$out/receipt.txt"
grep -Fq 'generated_rust_sha256=' "$out/receipt.txt"
grep -Fq 'generated_rlib_sha256=' "$out/receipt.txt"
stored_hash="$(sha256sum "$out/receipt.txt" | cut -d' ' -f1)"

# A successful prior bundle must not be clobbered, even if the new request is
# valid or attempts another root.
if bash scripts/compile-bundle.sh PropertyDef Property.hop \
    examples/PropertyDef.lean "$out" property_hop \
    > "$sandbox/existing.log" 2>&1; then
  echo "Bundle CLI overwrote prior successful output" >&2
  exit 1
fi
test "$(sha256sum "$out/receipt.txt" | cut -d' ' -f1)" = "$stored_hash"

# An unsupported imported runtime declaration must neither publish partial
# source nor a misleading receipt.
if bash scripts/compile-bundle.sh PropertyDef String.intercalate \
    examples/PropertyDef.lean "$sandbox/refused" public_root \
    > "$sandbox/refused.log" 2>&1; then
  echo "Bundle CLI accepted an unsupported imported runtime declaration" >&2
  exit 1
fi
test ! -e "$sandbox/refused"
grep -q 'Rust native backend refused' "$sandbox/refused.log"

# Refuse unsafe names and traversal before invoking Lean or publishing.
if bash scripts/compile-bundle.sh PropertyDef 'Property.hop"; #eval 0' \
   examples/PropertyDef.lean "$sandbox/unsafe" public_root > /dev/null 2>&1; then
  echo "Unsafe Lean declaration accepted" >&2
  exit 1
fi
test ! -e "$sandbox/unsafe"
if bash scripts/compile-bundle.sh PropertyDef Property.hop \
   examples/PropertyDef.lean "$sandbox/../escape" public_root > /dev/null 2>&1; then
  echo "Output traversal accepted" >&2
  exit 1
fi

# Check that the source in the accepted bundle matches exact original input.
cmp examples/PropertyDef.lean "$out/PropertyDef.lean"
sha256sum "$out/generated.rs" "$out/receipt.txt" "$out/closure.txt"
echo 'PASS: atomic receipt bundle, compiled Rust, closure, no-overwrite, refusals, unsafe paths'
