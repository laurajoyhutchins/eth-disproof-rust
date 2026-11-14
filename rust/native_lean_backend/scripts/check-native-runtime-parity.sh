#!/usr/bin/env bash
# Executable, identical-source parity: original Lean interpreter, Lean C
# backend, and the generated standalone Rust. Never substitute an algorithm.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LEAN_PREFIX:?Set LEAN_PREFIX to exact Lean 4.34.1 distribution}"
export PATH="${LEAN_PREFIX}/bin:${PATH}"
export LEAN_PATH="$(pwd)/examples:$(pwd):${LEAN_PREFIX}/lib/lean${LEAN_PATH:+:${LEAN_PATH}}"
export LD_LIBRARY_PATH="${LEAN_PREFIX}/lib/lean${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
NATIVE_LIB="$(pwd)/target/release/liblean_rust_native_backend.so"
test -f "$NATIVE_LIB"
test -x /usr/bin/time
test "$(lean --version)" = "Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)"
test "$(rustc --version)" = "rustc 1.99.1 (58cf8f9c3 2026-10-13)"

mkdir -p artifacts/parity-native
out="$(pwd)/artifacts/parity-native"
lean -o examples/PropertyDef.olean examples/PropertyDef.lean
lean --load-dynlib="$NATIVE_LIB" examples/PropertyCodegen.lean > "$out/emitter.log"
lean -c "$out/PropertyDef.c" examples/PropertyDef.lean > "$out/property-c.log"
lean -c "$out/PropertyNativeBenchmark.c" examples/PropertyNativeBenchmark.lean > "$out/bench-c.log"

# leanc is the pinned Lean 4.34.1 linker wrapper; generated C depends on
# Lean at runtime, unlike the emitted Rust. Both execute Property.hop.
leanc -O2 -o "$out/lean-native" \
  "$out/PropertyDef.c" "$out/PropertyNativeBenchmark.c" > "$out/lean-build.log" 2>&1
rustc --edition=2021 -O -D warnings -F unsafe-code \
  -o "$out/rust-native" examples/property_native_benchmark.rs > "$out/rust-build.log" 2>&1

lean --run examples/PropertyNativeBenchmark.lean > "$out/lean-interpreted.txt"
"$out/lean-native" > "$out/lean-native.txt"
"$out/rust-native" > "$out/rust-native.txt"
if ! cmp -s "$out/lean-interpreted.txt" "$out/lean-native.txt" ||
   ! cmp -s "$out/lean-native.txt" "$out/rust-native.txt"; then
  echo "FATAL: original Lean interpretation, original Lean C, and emitted Rust do not agree" >&2
  echo "--- Lean interpreter:" >&2
  cat "$out/lean-interpreted.txt" >&2
  echo "--- Lean C:" >&2
  cat "$out/lean-native.txt" >&2
  echo "--- emitted Rust:" >&2
  cat "$out/rust-native.txt" >&2
  exit 1
fi
if ! grep -Eq '^[0-9]+$' "$out/lean-native.txt"; then
  echo "No valid numeric checksum emitted" >&2; exit 1
fi
printf 'trial\tbackend\twall_seconds\tpeak_rss_kb\n' > "$out/measurements.tsv"
for trial in 1 2 3; do
  for backend in lean-native rust-native; do
    /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
      -o "$out/${backend}-${trial}.time" \
      "$out/$backend" > "$out/${backend}-${trial}.txt"
    cmp "$out/lean-interpreted.txt" "$out/${backend}-${trial}.txt"
    awk -v trial="$trial" -v backend="$backend" \
      '{split($1,w,"=");split($2,m,"=");print trial "\t" backend "\t" w[2] "\t" m[2]}' \
      "$out/${backend}-${trial}.time" >> "$out/measurements.tsv"
  done
done
{
  echo "status=PASS_ORIGINAL_LEAN_C_VS_EMITTED_RUST_IDENTICAL_CHECKSUM"
  echo "lean_revision=$(lean --version)"
  echo "rust_revision=$(rustc --version)"
  echo "source_revision=$(git rev-parse --verify HEAD 2>/dev/null || echo unavailable)"
  echo "case=Property.hop"
  echo "iterations=16384"
  echo "inputs=matching_64bit_lcg_and_i_mod_17"
  echo "lean_native_uses_lean_runtime=yes"
  echo "rust_native_uses_lean_runtime=no"
  echo "cache_status=warm_uncontrolled"
  echo "comparison_scope=runtime_only_not_equal_compilation_cost"
  echo "legacy_json_backend=UNSUPPORTED_THIS_IR_FIXTURE"
  echo "checksum=$(cat "$out/lean-native.txt")"
  sha256sum examples/PropertyDef.lean examples/PropertyNativeBenchmark.lean \
    examples/property_native_benchmark.rs examples/generated_property.rs \
    "$out/PropertyDef.c" "$out/PropertyNativeBenchmark.c" \
    "$out/lean-native" "$out/rust-native" \
    "$out/measurements.tsv"
} > "$out/receipt.txt"
cat "$out/receipt.txt"
cat "$out/measurements.tsv"
