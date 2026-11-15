#!/usr/bin/env bash
# Original Lean -> C vs live-Lean-IR -> Rust. Three fresh compilations, not a
# substituted Rust implementation. Never infer universal speedup from one root.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LEAN_PREFIX:?Set LEAN_PREFIX to the pinned Lean 4.34.1 distribution}"
export PATH="$LEAN_PREFIX/bin:$PATH"
export LEAN_PATH="$(pwd)/examples:$(pwd):$LEAN_PREFIX/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
export LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
lib="$(pwd)/target/release/liblean_rust_native_backend.so"
out="$(pwd)/artifacts/compare-native"
parity="$(pwd)/artifacts/parity-native"
test -f "$lib"
test -s "$parity/lean-interpreted.txt"
test -s "$parity/lean-native.txt"
test -s "$parity/rust-native.txt"
cmp "$parity/lean-interpreted.txt" "$parity/lean-native.txt"
cmp "$parity/lean-interpreted.txt" "$parity/rust-native.txt"
test "$(lean --version)" = 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'
test "$(rustc --version)" = 'rustc 1.99.1 (58cf8f9c3 2026-10-13)'
test -x /usr/bin/time
mkdir -p "$out"
printf 'trial\tbackend\tphase\twall_seconds\tpeak_rss_kib\n' > "$out/compile-phases.tsv"
printf 'trial\tbackend\tbytes\tsha256\n' > "$out/executables.tsv"

# Each timed phase includes a fresh process and writes raw stdout/stderr.
# Runtimes verified after building to catch optimizer- or linkage-dependent bugs.
measure() {
  local trial="$1" backend="$2" phase="$3"
  shift 3
  local file="$out/${trial}-${backend}-${phase}"
  /usr/bin/time -f '%e\t%M' -o "$file.time" "$@" > "$file.log" 2>&1
  local elapsed rss
  IFS=$'\t' read -r elapsed rss < "$file.time"
  printf '%s\t%s\t%s\t%s\t%s\n' "$trial" "$backend" "$phase" "$elapsed" "$rss" >> "$out/compile-phases.tsv"
}

# Both drivers perform the same deterministic work and call the same original
# Property.hop declaration. The Lean driver is Lean code compiled to C;
# the Rust driver is thin host scaffolding including the IR-emitted function.
# C output depends on Lean's runtime. Rust output does not.
run_c() {
  local trial="$1"
  ( cd examples; measure "$trial" lean-c source-to-c \
      lean -c "$out/PropertyDef-${trial}.c" PropertyDef.lean )
  ( cd examples; measure "$trial" lean-c driver-to-c \
      lean -c "$out/PropertyNativeBenchmark-${trial}.c" PropertyNativeBenchmark.lean )
  measure "$trial" lean-c c-compile-and-link leanc -O2 \
    -o "$out/lean-native-${trial}" \
    "$out/PropertyDef-${trial}.c" "$out/PropertyNativeBenchmark-${trial}.c"
  "$out/lean-native-${trial}" > "$out/lean-native-${trial}.txt"
  cmp "$parity/lean-interpreted.txt" "$out/lean-native-${trial}.txt"
  printf '%s\tlean-c\t%s\t%s\n' "$trial" \
    "$(stat -c %s "$out/lean-native-${trial}")" \
    "$(sha256sum "$out/lean-native-${trial}" | cut -d' ' -f1)" >> "$out/executables.tsv"
}

run_rust() {
  local trial="$1"
  measure "$trial" lean-rust source-to-olean \
    lean -o examples/PropertyDef.olean examples/PropertyDef.lean
  measure "$trial" lean-rust in-process-ir-to-rust \
    lean --load-dynlib="$lib" examples/PropertyCodegen.lean
  test -s examples/generated_property.rs
  # This is source generated through live IR, never a handwritten algorithm.
  cp examples/generated_property.rs "$out/generated-property-${trial}.rs"
  measure "$trial" lean-rust rust-compile-and-link \
    rustc --edition=2021 -O -D warnings -F unsafe-code \
      -o "$out/rust-native-${trial}" examples/property_native_benchmark.rs
  "$out/rust-native-${trial}" > "$out/rust-native-${trial}.txt"
  cmp "$parity/lean-interpreted.txt" "$out/rust-native-${trial}.txt"
  printf '%s\tlean-rust\t%s\t%s\n' "$trial" \
    "$(stat -c %s "$out/rust-native-${trial}")" \
    "$(sha256sum "$out/rust-native-${trial}" | cut -d' ' -f1)" >> "$out/executables.tsv"
}

for trial in 1 2 3; do
  if (( trial % 2 == 0 )); then
    run_rust "$trial"
    run_c "$trial"
  else
    run_c "$trial"
    run_rust "$trial"
  fi
done

# Stable emitted algorithms are required; native ELF bytes can vary with paths.
cmp "$out/generated-property-1.rs" "$out/generated-property-2.rs"
cmp "$out/generated-property-1.rs" "$out/generated-property-3.rs"
ldd "$out/lean-native-3" > "$out/lean-c-dynamic-dependencies.txt"
ldd "$out/rust-native-3" > "$out/rust-dynamic-dependencies.txt"
{
  echo 'status=PASS_C_AND_RUST_COMPILE_AND_EXECUTE_SOURCE_IDENTICALLY'
  echo "source_commit=$(git rev-parse --verify HEAD 2>/dev/null || echo unavailable)"
  echo "source_sha256=$(sha256sum examples/PropertyDef.lean | cut -d' ' -f1)"
  echo "original_lean_checksum=$(cat "$parity/lean-interpreted.txt")"
  echo "lean_version=$(lean --version)"
  echo "rust_version=$(rustc --version)"
  echo "leanc_version=$(leanc --version 2>&1 | head -n 1 || true)"
  echo "cc_version=$(cc --version | head -n 1)"
  echo "kernel=$(uname -srmo)"
  echo "runner_cpus=$(nproc)"
  echo 'sample_count=3'
  echo 'compile_phases=comparable_source_semantics_NOT_equivalent_frontend_work'
  echo 'source_to_olean=additional_lean_ir_preparation_for_rust_path'
  echo 'source_to_c=frontend_and_c_codegen_together'
  echo 'lean_rust_ir_to_rust=imports_precompiled_olean_and_loads_plugin'
  echo 'c_and_rust_drivers=language_specific_thin_loop_scaffolding'
  echo 'cache_and_cpu_frequency=uncontrolled'
  echo 'runtime_samples=parity-native/measurements-ns.tsv'
  echo 'no_link_time_or_binary_size_winner_claim=dynamic_runtime_deps_differ'
  sha256sum "$out/compile-phases.tsv" "$out/executables.tsv" \
    "$out/generated-property-3.rs" "$out/PropertyDef-3.c" \
    "$out/PropertyNativeBenchmark-3.c" \
    "$out/lean-c-dynamic-dependencies.txt" "$out/rust-dynamic-dependencies.txt"
} > "$out/receipt.txt"
cat "$out/receipt.txt"
cat "$out/compile-phases.tsv"
cat "$out/executables.tsv"
