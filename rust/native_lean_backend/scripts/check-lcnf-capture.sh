#!/usr/bin/env bash
# Compare canonical Rust emission with and without reading Lean's saved LCNF.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${NATIVE_LIB:?Run after building the in-process Rust backend}"
mkdir -p artifacts

lean -o LCNFCapture.olean LCNFCapture.lean
export LEAN_PATH="$(pwd):${LEAN_PATH:-}"

rm -f artifacts/lcnf-baseline.rs artifacts/lcnf-with-pass.rs artifacts/lcnf-capture.json
lean --load-dynlib="$NATIVE_LIB" examples/LCNFBaseline.lean
lean --load-dynlib="$NATIVE_LIB" examples/LCNFCaptureFixture.lean

# Reading saved LCNF must never affect the canonical IR -> Rust emitter.
cmp artifacts/lcnf-baseline.rs artifacts/lcnf-with-pass.rs
test -s artifacts/lcnf-capture.json
for name in LCNFProbe.select LCNFProbe.bump LCNFProbe.tailOrEmpty; do
  grep -Fq "\"name\":\"$name\"" artifacts/lcnf-capture.json
done
grep -Fq '"source":"Lean.Compiler.LCNF.getLocalImpureDecl?"' artifacts/lcnf-capture.json
grep -Fq '"phase":"impure"' artifacts/lcnf-capture.json

cat > artifacts/lcnf-executable.rs <<'RUST'
include!("lcnf-with-pass.rs");
fn main() {
    assert_eq!(select(2, 3), 8);
    assert_eq!(select(5, 1), 7);
    assert_eq!(select(u64::MAX, 0), 6);
}
RUST
rustc --edition=2024 -D warnings -o artifacts/lcnf-executable artifacts/lcnf-executable.rs
artifacts/lcnf-executable
echo "Final saved impure LCNF inspected; Rust byte-parity and execution: PASS"
