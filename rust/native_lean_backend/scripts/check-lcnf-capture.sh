#!/usr/bin/env bash
# Read-only LCNF pass smoke test against the existing canonical IR -> Rust path.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${NATIVE_LIB:?Run after building the in-process Rust backend}"
mkdir -p artifacts

lean -o LCNFCapture.olean LCNFCapture.lean
lean -o LCNFCaptureActive.olean LCNFCaptureActive.lean
export LEAN_PATH="$(pwd):${LEAN_PATH:-}"

rm -f artifacts/lcnf-baseline.rs artifacts/lcnf-with-pass.rs artifacts/lcnf-capture.json
lean --load-dynlib="$NATIVE_LIB" examples/LCNFBaseline.lean
lean --load-dynlib="$NATIVE_LIB" examples/LCNFCaptureFixture.lean

# The observational pass must not affect Rust generation, even for a
# branch/join and a direct call to an additional source function.
cmp artifacts/lcnf-baseline.rs artifacts/lcnf-with-pass.rs
test -s artifacts/lcnf-capture.json
for name in LCNFProbe.select LCNFProbe.bump LCNFProbe.tailOrEmpty; do
  grep -Fq "\"name\":\"$name\"" artifacts/lcnf-capture.json
done
grep -Fq '"hook":"after-saveImpure"' artifacts/lcnf-capture.json
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
echo "Final impure LCNF observed; Rust byte-parity and execution: PASS"
