#!/usr/bin/env bash
# Exact original Lean 4.34.1 value-oracle comparison with standalone Rust.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${NATIVE_LIB:?Run check.sh so the pinned in-process compiler is loaded}"
: "${LEAN_PREFIX:?Requires the pinned Lean toolchain}"
mkdir -p artifacts
lean --load-dynlib="$NATIVE_LIB" examples/Item30Conformance.lean
# Seven non-Nat source adapters share the canonical GMP-backed Rc value API.
adapter_count=0
while IFS=$'\t' read -r lean_name method shape; do
  [[ -z "$lean_name" || "$lean_name" == \#* ]] && continue
  if ! grep -Fq ".${method}(" examples/generated_sem_*.rs; then
    echo "runtime method missing its original-source fixture: $lean_name" >&2
    exit 1
  fi
  adapter_count=$((adapter_count + 1))
done < runtime-primitive-registry.tsv
if [[ "$adapter_count" -ne 7 ]]; then
  echo "expected seven additional adapters, got $adapter_count" >&2
  exit 1
fi
# The three Nat operations use mainline GMP, not an alternative BigNat kernel.
for name in nat_add nat_sub nat_mul; do
  if ! grep -Fq '.nat_binary(' "examples/generated_sem_${name}.rs"; then
    echo "missing GMP-backed original-source fixture: ${name}" >&2
    exit 1
  fi
done
cat > examples/item30-run.rs <<'RUST'
// Canonical GMP Nat uses audited FFI in standalone Rust; no Lean runtime linked.
#[allow(dead_code)] mod nat_add { include!("generated_sem_nat_add.rs"); }
#[allow(dead_code)] mod nat_add_closure { include!("generated_sem_nat_add_closure.rs"); }
#[allow(dead_code)] mod nat_sub { include!("generated_sem_nat_sub.rs"); }
#[allow(dead_code)] mod nat_mul { include!("generated_sem_nat_mul.rs"); }
#[allow(dead_code)] mod int_add { include!("generated_sem_int_add.rs"); }
#[allow(dead_code)] mod str_append { include!("generated_sem_str_append.rs"); }
#[allow(dead_code)] mod str_bytes { include!("generated_sem_str_bytes.rs"); }
#[allow(dead_code)] mod str_chars { include!("generated_sem_str_chars.rs"); }
#[allow(dead_code)] mod array_push { include!("generated_sem_array_push.rs"); }
#[allow(dead_code)] mod array_size { include!("generated_sem_array_size.rs"); }
#[allow(dead_code)] mod list_reverse { include!("generated_sem_list_reverse.rs"); }
include!("generated_semantic_cases.rs");
RUST
checks="$(grep -c 'assert_eq!' examples/generated_semantic_cases.rs)"
cp examples/generated_semantic_cases.rs artifacts/item30-oracles.rs
if [[ "$checks" -ne 101 ]]; then
  echo "expected 101 real Lean type-semantic cases, received $checks" >&2; exit 1
fi
rustc --edition=2021 -D warnings -o artifacts/item30-conformance examples/item30-run.rs
artifacts/item30-conformance

# Independently run a release Cargo binary without a Lean runtime.
rm -rf artifacts/item30-standalone
mkdir -p artifacts/item30-standalone/src
cp examples/item30-run.rs artifacts/item30-standalone/src/main.rs
cp examples/generated_sem_*.rs examples/generated_semantic_cases.rs artifacts/item30-standalone/src/
cat > artifacts/item30-standalone/Cargo.toml <<'CARGO'
[package]
name = "lean_native_item30_conformance"
version = "0.1.0"
edition = "2021"

[workspace]
CARGO
env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
  cargo test --offline --manifest-path artifacts/item30-standalone/Cargo.toml
env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
  cargo build --release --offline --manifest-path artifacts/item30-standalone/Cargo.toml
env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
  artifacts/item30-standalone/target/release/lean_native_item30_conformance
if ldd artifacts/item30-standalone/target/release/lean_native_item30_conformance | grep -i lean; then
  echo "emitted item30 executable unexpectedly links Lean runtime" >&2; exit 1
fi
cargo clippy --offline --manifest-path artifacts/item30-standalone/Cargo.toml --all-targets -- -D warnings
# Verify unsupported operations and failed compilation preserve every artifact.
for kind in nat_bitwise string_push array_get; do
  printf 'preexisting-source-must-survive\n' > "examples/sem_rejected_${kind}.rs"
done
if lean --load-dynlib="$NATIVE_LIB" examples/Item30Errors.lean \
    > artifacts/item30-rejection.log 2>&1; then
  echo "item30 unsupported operations incorrectly reported success" >&2; exit 1
fi
for kind in nat_bitwise string_push array_get; do
  if [[ "$(cat "examples/sem_rejected_${kind}.rs")" != "preexisting-source-must-survive" ]]; then
    echo "item30 refusal damaged ${kind} output artifact" >&2; exit 1
  fi
done
for declaration in unsupportedNatBitwise unsupportedStringPush unsupportedArrayGet; do
  if ! grep -Fq "\"declaration\":\"Item30Errors.${declaration}\"" \
      artifacts/item30-rejection.log; then
    cat artifacts/item30-rejection.log >&2
    echo "item30 missing named JSON refusal for ${declaration}" >&2; exit 1
  fi
done
rm -f examples/sem_rejected_nat_bitwise.rs examples/sem_rejected_string_push.rs examples/sem_rejected_array_get.rs
echo "item30 supported object semantics=PASS"
echo "item30 value_oracle_assertions=$checks"
echo "item30 verified_runtime_adapters=$adapter_count"
