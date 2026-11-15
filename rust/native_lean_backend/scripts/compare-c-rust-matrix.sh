#!/usr/bin/env bash
# Exact-source Lean C vs in-process Lean-IR Rust: arrays, closures, GMP Nat.
# Both compiler backends consume the original BenchmarkKernels.lean. The Rust
# CLI is only the input/checksum driver; no source algorithm is reimplemented.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LEAN_PREFIX:?Set LEAN_PREFIX to pinned Lean 4.34.1}"
export PATH="$LEAN_PREFIX/bin:$PATH"
export LEAN_PATH="$(pwd)/examples:$(pwd):$LEAN_PREFIX/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
export LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
test "$(lean --version)" = 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'
test "$(rustc --version)" = 'rustc 1.99.1 (58cf8f9c3 2026-10-13)'
test -x /usr/bin/time
plugin="$(pwd)/target/release/liblean_rust_native_backend.so"
test -s "$plugin"
out="$(pwd)/artifacts/bench-matrix"
rm -rf "$out"
mkdir -p "$out"
printf 'backend\tphase\twall_seconds\tpeak_rss_kib\n' > "$out/compile-phases.tsv"
measure() {
  local backend="$1" phase="$2"
  shift 2
  local file="$out/$backend-$phase"
  /usr/bin/time -f '%e\t%M' -o "$file.time" "$@" > "$file.log" 2>&1
  local wall rss
  IFS=$'\t' read -r wall rss < "$file.time"
  printf '%s\t%s\t%s\t%s\n' "$backend" "$phase" "$wall" "$rss" >> "$out/compile-phases.tsv"
}
# Pinned original source -> .olean (used as Rust emitter's imported IR).
measure lean-rust source-to-olean \
  lean -o examples/BenchmarkKernels.olean examples/BenchmarkKernels.lean

# The regular Lean C backend sees the exact same original definition.
# Compile within examples so Lean module identity remains BenchmarkKernels.
measure lean-c kernel-to-c \
  bash -c 'cd examples && lean -c "$1" BenchmarkKernels.lean' bash "$out/BenchmarkKernels.c"
measure lean-c driver-to-c \
  bash -c 'cd examples && lean -c "$1" BenchmarkDriver.lean' bash "$out/BenchmarkDriver.c"
measure lean-c native-compile-and-link leanc -O2 \
  -o "$out/lean-c" "$out/BenchmarkKernels.c" "$out/BenchmarkDriver.c"

# The only implementation of benchmark functions emitted to Rust is derived
# from live Lean IR. Fail closed if the source contract or emitted roots drift.
measure lean-rust in-process-ir-codegen \
  lean --load-dynlib="$plugin" examples/BenchmarkCodegen.lean
generated="$out/generated-package"
test -s "$generated/src/lib.rs"
for root in arrayStep closureStep natStep natAccumulate; do
  if ! grep -Fq "Generated directly from Lean IR declaration: BenchmarkKernels.$root" \
    "$generated/src/lib.rs"; then
    echo "FATAL: source-derived root $root absent from emitted Rust" >&2
    exit 1
  fi
done
# This source fixture has three last-use Array.push calls and one preserved
# live alias across the subsequent join and branches. Assert the emitted
# implementation chooses the owned path without consuming the shared x_8.
# The numbered VarIds come from pinned Lean 4.34.1 IR and are independently
# checked by the original Lean/C/Rust output parity below.
if ! grep -Fq 'x_13.array_push_owned(' "$generated/src/lib.rs" ||
   ! grep -Fq 'x_4.array_push_owned(' "$generated/src/lib.rs" ||
   ! grep -Fq 'x_6.array_push_owned(' "$generated/src/lib.rs" ||
   ! grep -Fq 'x_8.clone().array_set_tagged(' "$generated/src/lib.rs"; then
  echo 'FATAL: ownership lowering failed to consume dead arrays or preserve the live alias' >&2
  exit 1
fi
# The original benchmark's source-level binary closures lower into
# arity-three boxed Lean functions with two captures in Lean 4.34.1 IR.
# This assertion requires the actual generated algorithm to select the
# specialized capture representation and unary AP, not just its runtime.
codegen="$(sed -n '/^\/\/ Native in-process Lean IR closure/,/^#\[cfg(test)\]/p' "$generated/src/lib.rs")"
if ! grep -Fq '__LeanValue::pap3(' <<< "$codegen" ||
   ! grep -Eq '\.apply1(_owned)?\(' <<< "$codegen"; then
  echo 'FATAL: benchmark closure IR did not select inline PAP and unary AP' >&2
  grep -En 'pap3|pap\(|apply1|apply\(' <<< "$codegen" | head -n 25 >&2 || true
  exit 1
fi
cp examples/benchmark_matrix_driver.rs "$generated/src/main.rs"
measure lean-rust native-compile-and-link \
  cargo build --release --offline --manifest-path "$generated/Cargo.toml"
rustbin="$generated/target/release/lean_generated"
test -x "$rustbin"

rustc --edition=2021 -O -D warnings -F unsafe-code \
  -o "$out/bench-subprocess" examples/bench_matrix_subprocess.rs

# Real original Lean interpretation, native C, native Rust on the SAME inputs.
# Small checks guard semantics independently of the compiled binaries. Large
# workload checks guard C-vs-Rust at full benchmark size before timing.
printf 'workload\titerations\tlean_interpreter\tlean_c\tlean_rust\n' > "$out/parity.tsv"
printf 'workload\titerations\tbackend\twall_seconds\tpeak_rss_kib\n' > "$out/runtime-rss.tsv"
for spec in "array:262144" "closure:262144" "nat:12000"; do
  workload="${spec%%:*}"
  count="${spec##*:}"
  measure "oracle-$workload" interpreted \
    lean --run examples/BenchmarkDriver.lean "$workload" 32
  "$out/lean-c" "$workload" 32 > "$out/$workload-c-small.txt"
  "$rustbin" "$workload" 32 > "$out/$workload-rust-small.txt"
  cmp "$out/oracle-$workload-interpreted.log" "$out/$workload-c-small.txt"
  cmp "$out/oracle-$workload-interpreted.log" "$out/$workload-rust-small.txt"

  "$out/lean-c" "$workload" "$count" > "$out/$workload-expected.txt"
  "$rustbin" "$workload" "$count" > "$out/$workload-rust-full.txt"
  cmp "$out/$workload-expected.txt" "$out/$workload-rust-full.txt"
  printf '%s\t%s\tPASS\tPASS\tPASS\n' "$workload" "$count" >> "$out/parity.tsv"

  for backend in lean-c lean-rust; do
    executable="$out/lean-c"
    if [[ "$backend" == lean-rust ]]; then executable="$rustbin"; fi
    for trial in 1 2 3; do
      metric="$out/$workload-$backend-rss-$trial.time"
      /usr/bin/time -f '%e\t%M' -o "$metric" \
        "$executable" "$workload" "$count" > "$out/$workload-$backend-rss-$trial.out"
      cmp "$out/$workload-expected.txt" "$out/$workload-$backend-rss-$trial.out"
      IFS=$'\t' read -r wall rss < "$metric"
      printf '%s\t%s\t%s\t%s\t%s\n' "$workload" "$count" "$backend" "$wall" "$rss" >> "$out/runtime-rss.tsv"
    done
  done
  "$out/bench-subprocess" "$out/lean-c" "$rustbin" "$workload" "$count" \
    "$out/$workload-expected.txt" \
    > "$out/$workload-runtime-ns.tsv" 2> "$out/$workload-summary.txt"
  # A zero-iteration control measures launch, dynamic-linker and driver
  # startup without invoking the emitted Lean function. Report separately.
  printf '0\n' > "$out/$workload-zero-expected.txt"
  "$out/bench-subprocess" "$out/lean-c" "$rustbin" "$workload" 0 \
    "$out/$workload-zero-expected.txt" \
    > "$out/$workload-startup-ns.tsv" 2> "$out/$workload-startup-summary.txt"
done
ldd "$out/lean-c" > "$out/lean-c-dependencies.txt"
ldd "$rustbin" > "$out/rust-dependencies.txt"
{
  echo 'status=PASS_SOURCE_IDENTICAL_LEAN_C_VS_IR_RUST_MATRIX'
  echo "git_sha=$(git rev-parse HEAD)"
  echo "lean=$(lean --version)"
  echo "rust=$(rustc --version)"
  echo "leanc=$(leanc --version 2>&1 | head -1 || true)"
  echo "kernel=$(uname -srmo)"
  echo "cpus=$(nproc)"
  echo 'workloads=array,closure,nat'
  echo 'original_lean_small_oracle=32_per_workload'
  echo 'large_workload_parity=lean_c_equals_rust'
  echo 'runtime_samples_per_backend=12_per_workload'
  echo 'zero_iteration_startup_control=12_samples_per_backend'
  echo 'compile_samples_per_backend=1_not_a_statistical_result'
  echo 'runtime_scope=warm_subprocess_launch_to_checked_exit'
  echo 'runtime_linkage=lean_c_uses_lean_runtime;rust_uses_gmp_without_lean_runtime'
  echo 'driver_scope=language_specific_input_and_checksum_scaffolding'
  echo 'host_conditions=CI_cache_and_frequency_uncontrolled'
  echo 'unmodified_external_projects=NOT_PERFORMANCE_BENCHMARKED'
  echo 'no_general_speedup_or_formal_semantic_preservation_claim=true'
  echo 'array_ownership=source_ir_full_tail_proven_dead_for_push;live_old_alias_copied_for_set'
  sha256sum examples/BenchmarkKernels.lean examples/BenchmarkDriver.lean \
    examples/BenchmarkCodegen.lean examples/benchmark_matrix_driver.rs \
    "$out/BenchmarkKernels.c" "$out/BenchmarkDriver.c" \
    "$generated/src/lib.rs" "$out/compile-phases.tsv" "$out/parity.tsv" \
    "$out/runtime-rss.tsv" "$out/array-runtime-ns.tsv" \
    "$out/closure-runtime-ns.tsv" "$out/nat-runtime-ns.tsv" \
    "$out/array-startup-ns.tsv" "$out/closure-startup-ns.tsv" \
    "$out/nat-startup-ns.tsv"
} > "$out/receipt.txt"
cat "$out/receipt.txt"
cat "$out/compile-phases.tsv"
cat "$out/parity.tsv"
for k in array closure nat; do
  cat "$out/$k-summary.txt"
  cat "$out/$k-startup-summary.txt"
done
