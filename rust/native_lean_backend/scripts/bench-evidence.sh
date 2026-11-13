#!/usr/bin/env bash
# Opt-in raw per-invocation data, NOT cold-cache or cross-backend comparison.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LEAN_PREFIX:?Set LEAN_PREFIX to pinned Lean 4.34.1}"
export PATH="${LEAN_PREFIX}/bin:${PATH}"
export LEAN_PATH="$(pwd)/examples:$(pwd):${LEAN_PREFIX}/lib/lean${LEAN_PATH:+:${LEAN_PATH}}"
export LD_LIBRARY_PATH="${LEAN_PREFIX}/lib/lean${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
NATIVE_LIB="$(pwd)/target/release/liblean_rust_native_backend.so"
test -f "$NATIVE_LIB"
test -x /usr/bin/time
mkdir -p artifacts/bench-native
lean -o examples/PropertyDef.olean examples/PropertyDef.lean
{
  echo "source_revision=$(git rev-parse --verify HEAD 2>/dev/null || echo unavailable)"
  echo "lean_version=$(lean --version)"
  echo "rust_version=$(rustc --version)"
  echo "comparison_status=INCOMPLETE_NO_EQUIVALENT_C_OR_JSON_BASELINE"
  echo "measurement_scope=Lean_elaboration_ffi_codegen_and_test_vector_generation_combined"
} > artifacts/bench-native/manifest.txt
for trial in 1 2 3; do
  /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
    -o "artifacts/bench-native/lean-${trial}.time" \
    lean --load-dynlib="$NATIVE_LIB" examples/Property.lean \
    > "artifacts/bench-native/lean-${trial}.log" 2>&1
  sha256sum examples/generated_property.rs \
    > "artifacts/bench-native/generated-${trial}.sha256"
  /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
    -o "artifacts/bench-native/rust-build-${trial}.time" \
    rustc --edition=2021 -O -o examples/property-test examples/property_driver.rs
  /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
    -o "artifacts/bench-native/rust-run-${trial}.time" \
    examples/property-test > "artifacts/bench-native/rust-run-${trial}.log"
  wc -c examples/generated_property.rs examples/property-test \
    > "artifacts/bench-native/sizes-${trial}.txt"
done
for trial in 2 3; do
  cmp "artifacts/bench-native/generated-1.sha256" \
      "artifacts/bench-native/generated-${trial}.sha256"
done
echo "Raw trials recorded in artifacts/bench-native/. No speedup claimed."
