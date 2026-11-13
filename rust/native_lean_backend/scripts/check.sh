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
cat > examples/run.rs <<'RUST'
include!("generated_add_one.rs");
include!("generated_times_three.rs");
include!("generated_subtract_seven.rs");
include!("generated_two_args.rs");
include!("generated_multi.rs");
fn main() {
    assert_eq!(add_one(41), 42);
    assert_eq!(times_three(7), 21);
    assert_eq!(add_one(u64::MAX), 0);
    assert_eq!(subtract_seven(3), u64::MAX-3);
    assert_eq!(two_args(2, 3), 5);
    assert_eq!(multi(7), 36);
    assert_eq!(times_three(u64::MAX), u64::MAX - 2);
}
RUST
rustc --edition=2021 -o examples/native-test examples/run.rs
examples/native-test
cargo test --offline
cargo fmt -- --check
cargo clippy --offline --all-targets -- -D warnings
