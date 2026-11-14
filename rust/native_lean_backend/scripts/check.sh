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
# Real Lean IR join continuations (jdecl/jmp), including captured locals.
lean --load-dynlib="$NATIVE_LIB" examples/JoinFixture.lean
cat > examples/test-join.rs <<'RUST'
include!("generated_join.rs");
include!("generated_nested_join.rs");
fn main() { include!("generated_join_differential.rs"); }
RUST
rustc --edition=2024 -o examples/test-join examples/test-join.rs
examples/test-join
# One *standalone Cargo package*, three public roots, shared dependencies.
rm -rf examples/native-package
lean --load-dynlib="$NATIVE_LIB" examples/MultiRoot.lean
cargo test --offline --manifest-path examples/native-package/Cargo.toml
# Exactly one shared imported dependency in the emitted library.
if [[ "$(grep -c 'Generated directly from Lean IR declaration: Library.bump' examples/native-package/src/lib.rs)" != 1 ]]; then
  echo "multi-root emitter duplicated a shared dependency" >&2; exit 1
fi
package_hash_before="$(sha256sum examples/native-package/src/lib.rs | cut -d' ' -f1)"
rm -rf examples/native-package
lean --load-dynlib="$NATIVE_LIB" examples/MultiRoot.lean > /dev/null
package_hash_after="$(sha256sum examples/native-package/src/lib.rs | cut -d' ' -f1)"
if [[ "$package_hash_before" != "$package_hash_after" ]]; then
  echo "multi-root Cargo source is not deterministic" >&2; exit 1
fi
for name in RefusalPackageCollision RefusalPackageUnsupported; do
  rm -rf examples/rejected-package
  if lean --load-dynlib="$NATIVE_LIB" "examples/${name}.lean" > "examples/${name}.log" 2>&1; then
    echo "invalid multi-root package was accepted: $name" >&2; exit 1
  fi
  if [[ -e examples/rejected-package ]] || ! grep -q 'Rust native backend refused' "examples/${name}.log"; then
    echo "multi-root failure published partial code or lacked refusal: $name" >&2; exit 1
  fi
  rm -f "examples/${name}.log"
done
package_hash_before="$(sha256sum examples/native-package/src/lib.rs | cut -d' ' -f1)"
if lean --load-dynlib="$NATIVE_LIB" examples/RefusalPackageOverwrite.lean > examples/RefusalPackageOverwrite.log 2>&1; then
  echo "Cargo package overwrote existing destination" >&2; exit 1
fi
if [[ "$(sha256sum examples/native-package/src/lib.rs | cut -d' ' -f1)" != "$package_hash_before" ]]; then
  echo "refused overwrite modified the published Cargo package" >&2; exit 1
fi
rm -f examples/RefusalPackageOverwrite.log
# Immutable reference-counted runtime: Option, nested Option, Prod,
# constructors/projections, box/unbox and non-observable inc/dec bookkeeping.
rm -rf examples/object-package
lean --load-dynlib="$NATIVE_LIB" examples/Objects.lean
cargo test --offline --manifest-path examples/object-package/Cargo.toml
cargo clippy --offline --manifest-path examples/object-package/Cargo.toml --all-targets -- -D warnings
if [[ "$(grep -c 'Generated directly from Lean IR declaration: ObjectFixture.mkOpt' examples/object-package/src/lib.rs)" != 1 ]]; then
  echo "object constructor dependency was not emitted exactly once" >&2; exit 1
fi
# Keep unsupported arbitrary Nat and non-Option sum constructors fail closed.
for fixture in RefusalObjectNat RefusalObjectCtor; do
  rm -rf examples/rejected-object-package
  if lean --load-dynlib="$NATIVE_LIB" "examples/${fixture}.lean" > "examples/${fixture}.log" 2>&1; then
    echo "unsupported object program accepted: ${fixture}" >&2; exit 1
  fi
  if [[ -e examples/rejected-object-package ]] || ! grep -q 'Rust native backend refused' "examples/${fixture}.log"; then
    cat "examples/${fixture}.log" >&2
    echo "missing structured refusal: ${fixture}" >&2; exit 1
  fi
  rm -f "examples/${fixture}.log"
done
# Arbitrary precision Nat arithmetic over live compiler IR. GMP is linked into
# the standalone generated Rust (no Lean runtime required). Testing includes
# >1024-bit values and Lean's totalized division/modulus by zero.
rm -rf examples/nat-package
lean --load-dynlib="$NATIVE_LIB" examples/NatFixture.lean
cargo test --offline --manifest-path examples/nat-package/Cargo.toml
cargo clippy --offline --manifest-path examples/nat-package/Cargo.toml --lib -- -D warnings
# A Nat operation outside the supported primitive set must refuse the entire
# dependency closure and must not publish a partial Cargo package.
rm -rf examples/rejected-nat-package
if lean --load-dynlib="$NATIVE_LIB" examples/RefusalNatBitwise.lean > examples/RefusalNatBitwise.log 2>&1; then
  echo 'unsupported Nat bitwise primitive was accepted' >&2; exit 1
fi
if [[ -e examples/rejected-nat-package ]] || ! grep -q 'Rust native backend refused' examples/RefusalNatBitwise.log; then
  cat examples/RefusalNatBitwise.log >&2
  echo 'unsupported Nat compilation published partial output or lacked refusal' >&2; exit 1
fi
rm -f examples/RefusalNatBitwise.log
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
  echo "differential_assertions=11288"
  sha256sum NativeRust.lean native/abi.c src/lib.rs examples/Example.lean examples/Refusal.lean examples/JoinFixture.lean examples/MultiRoot.lean examples/native-package/src/lib.rs examples/native-package/Cargo.toml examples/object-package/src/lib.rs examples/object-package/Cargo.toml examples/Objects.lean examples/NatFixture.lean examples/nat-package/src/lib.rs examples/nat-package/Cargo.toml examples/generated_*.rs
} > artifacts/native-smoke-receipt.txt
cat artifacts/native-smoke-receipt.txt | head -9
