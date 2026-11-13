#!/usr/bin/env bash
# Exact Lean-compiler-IR inventory and complete supported-primitive differential
# matrix. Called from check.sh after restoring pinned Lean and Rust tools.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${NATIVE_LIB:?Run through check.sh after native Rust cdylib build}"
mkdir -p artifacts
rm -f artifacts/ir-constructors.tsv artifacts/ir-coverage.tsv \
      artifacts/primitive-conformance.tsv examples/generated_matrix_*.rs \
      examples/generated_matrix_assertions.rs examples/matrix_run.rs

# The active pinned Lean environment determines every constructor and tag.
lean examples/IRInventory.lean
rustc --edition=2021 -D warnings --test scripts/coverage-ledger.rs -o artifacts/coverage-ledger-tests
artifacts/coverage-ledger-tests
rustc --edition=2021 -D warnings scripts/coverage-ledger.rs -o artifacts/coverage-ledger
artifacts/coverage-ledger artifacts/ir-constructors.tsv \
  ir-coverage-classification.tsv artifacts/ir-coverage.tsv

# Independently evaluate Lean results; emit source via the live FFI compiler.
lean --load-dynlib="$NATIVE_LIB" examples/PrimitiveMatrix.lean
printf '# Generated functions only.\n' > examples/matrix_run.rs
printf 'primitive\tfunction\tassertions\toracle\n' > artifacts/primitive-conformance.tsv
count=0
while IFS=$'\t' read -r primitive rust_type operation kind; do
  [[ -z "$primitive" || "$primitive" == \#* ]] && continue
  suffix="${primitive##*.}"
  function="matrix_${rust_type}_${suffix}"
  source="examples/generated_${function}.rs"
  if [[ ! -f "$source" ]] || ! grep -Fq "pub fn ${function}(" "$source"; then
    echo "Supported compiler primitive lacks an emitted executable: $primitive ($source)" >&2
    exit 1
  fi
  if ! grep -Fq "#native_rust PrimitiveMatrix.${rust_type}_${suffix} as \"${function}\"" \
     examples/PrimitiveMatrix.lean; then
    echo "Coverage fixture does not bind primitive: $primitive" >&2
    exit 1
  fi
  printf 'include!("generated_%s.rs");\n' "$function" >> examples/matrix_run.rs
  printf '%s\t%s\t64\toriginal_Lean_4.34.1\n' "$primitive" "$function" \
    >> artifacts/primitive-conformance.tsv
  count=$((count + 1))
done < primitive-registry.tsv
if [[ "$count" -ne 30 ]]; then
  echo "Refusing incomplete primitive matrix: expected 30, got $count" >&2
  exit 1
fi
actual_assertions="$(grep -c 'assert_eq!' examples/generated_matrix_assertions.rs)"
if [[ "$actual_assertions" -ne "$((count*64))" ]]; then
  echo "Primitive oracle emitted $actual_assertions assertions, expected $((count*64))" >&2
  exit 1
fi
cat >> examples/matrix_run.rs <<'RUST'
fn main() {
    include!("generated_matrix_assertions.rs");
}
RUST
rustc --edition=2021 -D warnings -o artifacts/primitive-conformance-test examples/matrix_run.rs
artifacts/primitive-conformance-test
echo "IR constructor classification and $count primitives / $actual_assertions Lean/Rust comparisons: PASS"
