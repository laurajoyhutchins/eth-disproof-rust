#!/usr/bin/env bash
# Exact same Lean source, independently executed by Lean, Lean C and Rust.
set -euo pipefail
cd "$(dirname "$0")/.."
: "$LEAN_PREFIX"
export PATH="$LEAN_PREFIX/bin:$PATH"
export LEAN_PATH="$(pwd)/examples:$(pwd):$LEAN_PREFIX/lib/lean"
export LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean"
test "$(lean --version)" = 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'
test "$(rustc --version)" = 'rustc 1.99.1 (58cf8f9c3 2026-10-13)'
test -s examples/mut-package/src/lib.rs
for root in unique shared; do
  grep -Fq "Generated directly from Lean IR declaration: MutFixture.$root" examples/mut-package/src/lib.rs || exit 1
done
out="$(pwd)/artifacts/c-emitter-mut"
mkdir -p "$out"
(cd examples && lean -c "$out/MutKernels.c" MutKernels.lean)
(cd examples && lean -c "$out/MutCDriver.c" MutCDriver.lean)
leanc -O2 -o "$out/lean-c" "$out/MutKernels.c" "$out/MutCDriver.c"
cp examples/mut_c_driver.rs examples/mut-package/src/main.rs
env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH cargo build --release --offline --manifest-path examples/mut-package/Cargo.toml --bin lean_generated
rustbin="$(pwd)/examples/mut-package/target/release/lean_generated"
test -x "$rustbin"
set -- 0 0 0 1 1 0 1 1 2 3 7 11 11 7 42 42
for ((i=0; i<96; ++i)); do
  set -- "$@" "$i" "$((i * i + 42))"
done
set -- "$@" 18446744073709551615 18446744073709551616
set -- "$@" 340282366920938463463374607431768211456 340282366920938463463374607431768211479
set -- "$@" 115792089237316195423570985008687907853269984665640564039457584007913129639936 115792089237316195423570985008687907853269984665640564039457584007913129639953
lean --run examples/MutCDriver.lean "$@" > "$out/lean.txt"
"$out/lean-c" "$@" > "$out/c.txt"
env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH "$rustbin" "$@" > "$out/rust.txt"
if ! cmp -s "$out/lean.txt" "$out/c.txt" || ! cmp -s "$out/lean.txt" "$out/rust.txt"; then
  echo "Lean interpretation, C and Rust disagree on constructor mutation" >&2
  diff -u "$out/lean.txt" "$out/c.txt" || true
  diff -u "$out/lean.txt" "$out/rust.txt" || true
  exit 1
fi
{
 echo 'status=PASS_ORIGINAL_LEAN_C_RUST_CONSTRUCTOR_VALUE_PARITY'
 echo "revision=$(git rev-parse HEAD)"
 echo "lean=$(lean --version)"
 echo "rust=$(rustc --version)"
 echo "pairs=$(($# / 2))"
 echo 'physical_reference_count_equivalence=NOT_ESTABLISHED'
 sha256sum examples/MutKernels.lean examples/MutFixture.lean examples/MutCDriver.lean examples/mut_c_driver.rs examples/mut-package/src/lib.rs "$out/MutKernels.c" "$out/lean.txt" "$out/c.txt" "$out/rust.txt"
} > "$out/receipt.txt"
cat "$out/receipt.txt"
