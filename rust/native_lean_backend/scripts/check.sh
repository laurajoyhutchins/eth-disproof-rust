#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ "$("$LEAN_PREFIX/bin/lean" --version)" != *"version 4.34.1"* ]]; then
  echo "Expected Lean 4.34.1; refusing incompatible runtime layout" >&2; exit 2
fi
: "${LEAN_PREFIX:?Set LEAN_PREFIX to pinned Lean 4.34.1 distribution}"
export PATH="${LEAN_PREFIX}/bin:${PATH}"
export LEAN_PATH="${LEAN_PREFIX}/lib/lean${LEAN_PATH:+:${LEAN_PATH}}"
export LD_LIBRARY_PATH="${LEAN_PREFIX}/lib/lean${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
cargo build --offline --release
export NATIVE_LIB="$(pwd)/target/release/liblean_rust_native_backend.so"
lean -o NativeRust.olean NativeRust.lean
export LEAN_PATH="$(pwd):${LEAN_PATH}"
lean --load-dynlib="$NATIVE_LIB" examples/Example.lean
# Compile an imported Lean module separately, then compile its transitive
# dependency graph (including diamond sharing and recursive call cycles).
export LEAN_PATH="$(pwd)/examples:${LEAN_PATH}"
lean -o examples/Library.olean examples/Library.lean
lean --load-dynlib="$NATIVE_LIB" examples/Closure.lean
if [[ "$(grep -c 'Generated directly from Lean IR declaration: Library.bump' examples/generated_closure.rs)" != 1 ]]; then
  echo "shared Lean dependency was duplicated in Rust" >&2; exit 1
fi
# The backend must be deterministic even if Lean has already compiled roots.
closure_hash_before="$(sha256sum examples/generated_closure.rs | cut -d' ' -f1)"
lean --load-dynlib="$NATIVE_LIB" examples/Closure.lean > /dev/null
closure_hash_after="$(sha256sum examples/generated_closure.rs | cut -d' ' -f1)"
if [[ "$closure_hash_before" != "$closure_hash_after" ]]; then
  echo "non-deterministic in-process closure code generation" >&2; exit 1
fi
lean --load-dynlib="$NATIVE_LIB" examples/Refusal.lean
# Exercise the public *command* refusal path, not only a direct FFI call.
printf 'preserve-existing-artifact\n' > examples/rejected.rs
if lean --load-dynlib="$NATIVE_LIB" examples/RefusalCommand.lean > examples/rejected.log 2>&1; then
  echo "unsupported Lean declaration was accepted" >&2; exit 1
fi
if ! grep -q "Rust native backend refused" examples/rejected.log; then
  cat examples/rejected.log >&2
  echo "missing structured native compiler refusal" >&2; exit 1
fi
if [[ "$(cat examples/rejected.rs)" != "preserve-existing-artifact" ]]; then
  echo "failed compilation modified preexisting Rust output" >&2; exit 1
fi
rm -f examples/rejected.rs examples/rejected.log
# Even an elaborated executable declaration must refuse if its source
# depends on sorryAx. Do not publish code for untrusted proof holes.
printf 'preserve-sorry-output\n' > examples/rejected_sorry.rs
if lean --load-dynlib="$NATIVE_LIB" examples/RefusalSorry.lean > examples/rejected_sorry.log 2>&1; then
  echo "sorry-dependent declaration was accepted" >&2; exit 1
fi
if ! grep -q "dependency on sorry axiom" examples/rejected_sorry.log; then
  cat examples/rejected_sorry.log >&2
  echo "missing sorry-dependency refusal" >&2; exit 1
fi
if [[ "$(cat examples/rejected_sorry.rs)" != "preserve-sorry-output" ]]; then
  echo "sorry-dependent compilation changed existing output" >&2; exit 1
fi
rm -f examples/rejected_sorry.rs examples/rejected_sorry.log
# An unsupported primitive in a *transitive* callee must be refused,
# preserving previously generated output; no implicit host fallback.
for pair in "RefusalClosure:rejected_closure" "RefusalClosureSorry:rejected_sorry_closure"; do
  fixture="${pair%%:*}"
  destination="${pair##*:}"
  printf 'preserve-closure-artifact\n' > "examples/${destination}.rs"
  if lean --load-dynlib="$NATIVE_LIB" "examples/${fixture}.lean" > "examples/${destination}.log" 2>&1; then
    echo "unsupported ${fixture} dependency closure was accepted" >&2; exit 1
  fi
  if ! grep -q 'Rust native backend refused' "examples/${destination}.log"; then
    cat "examples/${destination}.log" >&2
    echo "missing structured refusal for ${fixture}" >&2; exit 1
  fi
  if [[ "$(cat "examples/${destination}.rs")" != 'preserve-closure-artifact' ]]; then
    echo "failed ${fixture} changed existing Rust output" >&2; exit 1
  fi
  rm -f "examples/${destination}.rs" "examples/${destination}.log"
done
cat > examples/run.rs <<'RUST'
include!("generated_add_one.rs");
include!("generated_times_three.rs");
include!("generated_subtract_seven.rs");
include!("generated_two_args.rs");
include!("generated_multi.rs");
include!("generated_choose.rs");
include!("generated_clamp.rs");
include!("generated_minus_if.rs");
include!("generated_eq_uint.rs");
include!("generated_add32.rs");
include!("generated_add_size.rs");
include!("generated_tiny8.rs");
include!("generated_tiny16.rs");
include!("generated_less32.rs");
include!("generated_leq64.rs");
include!("generated_closure.rs");
include!("generated_descend.rs");
include!("generated_mutual.rs");
fn main() {
    assert_eq!(add_one(41), 42);
    assert_eq!(times_three(7), 21);
    assert_eq!(add_one(u64::MAX), 0);
    assert_eq!(subtract_seven(3), u64::MAX-3);
    assert_eq!(two_args(2, 3), 5);
    assert_eq!(multi(7), 36);
    assert_eq!(times_three(u64::MAX), u64::MAX - 2);
    assert_eq!(choose(0), 1);
    assert_eq!(choose(4), 4);
    assert_eq!(clamp(8, 2), 2);
    assert_eq!(clamp(2, 8), 2);
    assert_eq!(minus_if(0), 0);
    assert_eq!(minus_if(8), 7);
    assert_eq!(eq_uint(4, 4), 1);
    assert_eq!(eq_uint(4, 5), 0);
    assert_eq!(add32(u32::MAX), u32::MAX);
    assert_eq!(add_size(usize::MAX), 6);
    assert_eq!(tiny8(u8::MAX), 4);
    assert_eq!(tiny16(u16::MAX), 11);
    assert_eq!(less32(2, 3), 1);
    assert_eq!(less32(3, 3), 0);
    assert_eq!(leq64(3, 3), 1);
    assert_eq!(leq64(4, 3), 0);
    include!("generated_differential.rs");
    include!("generated_closure_differential.rs");
}
RUST
rustc --edition=2021 -o examples/native-test examples/run.rs
examples/native-test
cargo test --offline
cargo fmt -- --check
cargo clippy --offline --all-targets -- -D warnings
# Receipt exists only after *all* end-to-end and negative checks pass.
mkdir -p artifacts
{
  echo "status=PASS"
  echo "source_revision=$(git rev-parse --verify HEAD 2>/dev/null || echo local-uncommitted)"
  echo "lean_toolchain=$(cat lean-toolchain)"
  "$LEAN_PREFIX/bin/lean" --version
  rustc --version
  cargo --version
  echo "differential_assertions=1984"
  sha256sum NativeRust.lean native/abi.c src/lib.rs examples/Example.lean examples/Refusal.lean examples/generated_*.rs
} > artifacts/native-smoke-receipt.txt
cat artifacts/native-smoke-receipt.txt | head -9
