#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LEAN_PREFIX:?Set LEAN_PREFIX to pinned Lean 4.34.1}"
export PATH="${LEAN_PREFIX}/bin:${PATH}"
export LEAN_PATH="$(pwd)/examples:$(pwd):${LEAN_PREFIX}/lib/lean${LEAN_PATH:+:${LEAN_PATH}}"
export LD_LIBRARY_PATH="${LEAN_PREFIX}/lib/lean${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
NATIVE_LIB="$(pwd)/target/release/liblean_rust_native_backend.so"
if [[ ! -f "$NATIVE_LIB" || ! -f NativeRust.olean ]]; then
  echo "Run scripts/check.sh first to build the native compiler" >&2
  exit 2
fi
if [[ "$(lean --version)" != *"version 4.34.1"* ]]; then
  echo "Refusing incompatible Lean runtime" >&2
  exit 2
fi
# Original Lean (not Rust codegen) evaluates all oracle values.
lean -o examples/PropertyDef.olean examples/PropertyDef.lean
lean --load-dynlib="$NATIVE_LIB" examples/Property.lean
rustc --edition=2021 -D warnings -o examples/property-test examples/property_driver.rs
examples/property-test
examples/property-test --seed 0
examples/property-test --seed 127

# The emitted Rust also compiles as an independent Cargo binary with no Lean
# runtime dependency and passes the normal strict linter.
mkdir -p artifacts/standalone-evidence/src
cp examples/generated_property.rs artifacts/standalone-evidence/src/generated_property.rs
cp examples/generated_property_cases.rs artifacts/standalone-evidence/src/generated_property_cases.rs
cp examples/property_driver.rs artifacts/standalone-evidence/src/main.rs
cat > artifacts/standalone-evidence/Cargo.toml <<'CARGO'
[package]
name = "native_lean_compiler_generated_evidence"
version = "0.0.0"
edition = "2021"

[workspace]
CARGO
cargo test --offline --manifest-path artifacts/standalone-evidence/Cargo.toml
cargo clippy --offline --manifest-path artifacts/standalone-evidence/Cargo.toml --all-targets -- -D warnings

# This PASS receipt is written only after all evidence checks succeeded.
{
  echo "status=PASS"
  echo "source_revision=$(git rev-parse --verify HEAD 2>/dev/null || echo unavailable)"
  echo "source_toolchain=$(cat lean-toolchain)"
  echo "lean_version=$(lean --version)"
  echo "rust_compiler=$(rustc --version)"
  echo "cargo_version=$(cargo --version)"
  rustc -vV | sed 's/^/rustc_verbose=/'
  echo "compiler_boundary=borrowed_Lean.IR.Decl_in_process"
  echo "declaration_closure=Property.hop"
  echo "property_seed_range=0..127"
  echo "cases_per_seed=8"
  echo "oracle=original_Lean_compiled_definition"
  echo "shrinking=finite_precomputed_candidates_only"
  echo "runtime_dependency=none_for_generated_Cargo_program"
  sha256sum NativeRust.lean examples/PropertyDef.lean examples/Property.lean \
    examples/property_driver.rs src/lib.rs native/abi.c \
    examples/generated_property.rs examples/generated_property_cases.rs \
    artifacts/standalone-evidence/Cargo.toml examples/property-test
} > artifacts/native-g1-evidence-receipt.txt
cat artifacts/native-g1-evidence-receipt.txt
