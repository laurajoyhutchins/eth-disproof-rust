#!/usr/bin/env bash
# Compare canonical Rust emission with and without reading Lean's saved LCNF.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${NATIVE_LIB:?Run after building the in-process Rust backend}"
mkdir -p artifacts

lean -o LCNFCapture.olean LCNFCapture.lean
export LEAN_PATH="$(pwd):${LEAN_PATH:-}"

rm -f artifacts/lcnf-baseline.rs artifacts/lcnf-observed.rs artifacts/lcnf-capture.json
lean --load-dynlib="$NATIVE_LIB" examples/LCNFBaseline.lean
lean --load-dynlib="$NATIVE_LIB" examples/LCNFCaptureFixture.lean

# Reading saved LCNF must never affect the canonical IR -> Rust emitter.
cmp artifacts/lcnf-baseline.rs artifacts/lcnf-observed.rs
test -s artifacts/lcnf-capture.json
for name in LCNFProbe.select LCNFProbe.bump LCNFProbe.tailOrEmpty; do
  grep -Fq "\"name\":\"$name\"" artifacts/lcnf-capture.json
done
grep -Fq '"source":"Lean.Compiler.LCNF.getLocalImpureDecl?"' artifacts/lcnf-capture.json
grep -Fq '"phase":"impure"' artifacts/lcnf-capture.json

cat > artifacts/lcnf-executable.rs <<'RUST'
include!("lcnf-observed.rs");
fn main() {
    assert_eq!(select(2, 3), 8);
    assert_eq!(select(5, 1), 7);
    assert_eq!(select(u64::MAX, 0), 6);
}
RUST
rustc --edition=2024 -D warnings -o artifacts/lcnf-executable artifacts/lcnf-executable.rs
artifacts/lcnf-executable
baseline_sha="$(sha256sum artifacts/lcnf-baseline.rs | cut -d' ' -f1)"
observed_sha="$(sha256sum artifacts/lcnf-observed.rs | cut -d' ' -f1)"
test "$baseline_sha" = "$observed_sha"
{
  printf 'lean=4.34.1\n'
  printf 'head=%s\n' "$(git rev-parse HEAD)"
  printf 'capture_source=Lean.Compiler.LCNF.getLocalImpureDecl?\n'
  printf 'captured_declarations=3\n'
  printf 'rust_sha256=%s\n' "$observed_sha"
  printf 'capture_sha256=%s\n' "$(sha256sum artifacts/lcnf-capture.json | cut -d' ' -f1)"
  printf 'rust_byte_parity=PASS\n'
  printf 'rust_execution_cases=3\n'
  printf 'result=PASS\n'
} > artifacts/lcnf-capture-receipt.txt
echo "Final saved impure LCNF inspected; Rust byte-parity and execution: PASS"
