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
  echo "differential_assertions=1600"
  sha256sum NativeRust.lean native/abi.c src/lib.rs examples/Example.lean examples/Refusal.lean examples/generated_*.rs
} > artifacts/native-smoke-receipt.txt
cat artifacts/native-smoke-receipt.txt | head -9
