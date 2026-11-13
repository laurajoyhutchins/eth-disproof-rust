#!/usr/bin/env bash
# Lightweight, opt-in raw compilation/runtime samples. No speedup claim:
# Lean's C backend compiles the source module; the in-process Rust backend
# imports precompiled IR and emits one root, so their phases differ.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LEAN_PREFIX:?Set LEAN_PREFIX to pinned Lean 4.34.1}"
export PATH="${LEAN_PREFIX}/bin:${PATH}"
export LEAN_PATH="$(pwd)/examples:$(pwd):${LEAN_PREFIX}/lib/lean${LEAN_PATH:+:${LEAN_PATH}}"
export LD_LIBRARY_PATH="${LEAN_PREFIX}/lib/lean${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
NATIVE_LIB="$(pwd)/target/release/liblean_rust_native_backend.so"
test -f "$NATIVE_LIB"
test -x /usr/bin/time
test -f examples/generated_property_cases.rs
mkdir -p artifacts/bench-native

# Input module and declaration are identical. The frontend work performed by
# the two Lean commands is NOT identical and is never reported as a speedup.
lean -o examples/PropertyDef.olean examples/PropertyDef.lean
{
  echo "source_revision=$(git rev-parse --verify HEAD 2>/dev/null || echo unavailable)"
  echo "lean_version=$(lean --version)"
  echo "rust_version=$(rustc --version)"
  echo "cc_version=$(cc --version | head -1)"
  echo "source_root=Property.hop"
  echo "source_sha256=$(sha256sum examples/PropertyDef.lean | cut -d' ' -f1)"
  echo "native_ir_input=precompiled_PropertyDef.olean"
  echo "native_ir_sha256=$(sha256sum examples/PropertyDef.olean | cut -d' ' -f1)"
  echo "lean_c_input=PropertyDef.lean_full_source_module"
  echo "comparison_status=INCOMPLETE_PHASES_DIFFER_NO_JSON_SOURCE_GRAPH_EQUIVALENT"
  echo "file_system_cache=UNCONTROLLED;fresh_process_each_trial"
  echo "runtime_equivalence=PROVED_BY_SEPARATE_LEAN_RUST_FIXTURES_NOT_MEASURED_FOR_C"
  echo "timing_unit=seconds;rss_unit=KiB;size_unit=bytes"
} > artifacts/bench-native/manifest.txt

for trial in 1 2 3; do
  # In-process Lean-to-Rust codegen (without the independently generated
  # oracle values). Includes Lean startup and loading the imported module.
  /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
    -o "artifacts/bench-native/native-codegen-${trial}.time" \
    lean --load-dynlib="$NATIVE_LIB" examples/PropertyCodegen.lean \
    > "artifacts/bench-native/native-codegen-${trial}.log" 2>&1
  sha256sum examples/generated_property.rs \
    > "artifacts/bench-native/native-generated-${trial}.sha256"

  # Lean's own pinned C backend generates C from the same original source.
  # Compilation includes source elaboration; it is not time-equivalent to an
  # imported-IR FFI emission.
  /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
    -o "artifacts/bench-native/lean-c-codegen-${trial}.time" \
    lean -c "artifacts/bench-native/PropertyDef-${trial}.c" examples/PropertyDef.lean \
    > "artifacts/bench-native/lean-c-codegen-${trial}.log" 2>&1
  /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
    -o "artifacts/bench-native/c-build-${trial}.time" \
    cc -std=c11 -O2 -fPIC -I"$LEAN_PREFIX/include" \
      -c "artifacts/bench-native/PropertyDef-${trial}.c" \
      -o "artifacts/bench-native/PropertyDef-${trial}.o"

  /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
    -o "artifacts/bench-native/rust-build-${trial}.time" \
    rustc --edition=2021 -O -o examples/property-test examples/property_driver.rs
  /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
    -o "artifacts/bench-native/rust-run-${trial}.time" \
    examples/property-test > "artifacts/bench-native/rust-run-${trial}.log"
  wc -c examples/generated_property.rs \
     "artifacts/bench-native/PropertyDef-${trial}.c" \
     "artifacts/bench-native/PropertyDef-${trial}.o" \
     examples/property-test > "artifacts/bench-native/sizes-${trial}.txt"
done
# Stable outputs are a precondition for interpreting repeated timings.
for trial in 2 3; do
  cmp "artifacts/bench-native/native-generated-1.sha256" \
      "artifacts/bench-native/native-generated-${trial}.sha256"
done
printf 'trial\tphase\twall_seconds\tpeak_rss_kb\n' > artifacts/bench-native/measurements.tsv
for trial in 1 2 3; do
  for phase in native-codegen lean-c-codegen c-build rust-build rust-run; do
    metrics="artifacts/bench-native/${phase}-${trial}.time"
    awk -v trial="$trial" -v phase="$phase" \
      '{split($1,a,"="); split($2,b,"="); print trial "\t" phase "\t" a[2] "\t" b[2]}' \
      "$metrics" >> artifacts/bench-native/measurements.tsv
  done
done
sha256sum artifacts/bench-native/manifest.txt \
    artifacts/bench-native/measurements.tsv \
    examples/PropertyDef.lean examples/PropertyCodegen.lean \
    examples/generated_property.rs > artifacts/bench-native/hashes.txt
cat artifacts/bench-native/manifest.txt
cat artifacts/bench-native/measurements.tsv
echo "No end-to-end Lean C/JSON/runtime speedup inferred."
