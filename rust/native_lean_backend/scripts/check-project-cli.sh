#!/usr/bin/env bash
# Real unchanged Lake project, separate from the native backend.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p artifacts
tmp="$(mktemp -d "$(pwd)/artifacts/project-cli-test.XXXXXXXX")"
trap 'rm -rf -- "$tmp"' EXIT
project="$tmp/source"
mkdir -p "$project"
printf 'leanprover/lean4:v4.34.1\n' > "$project/lean-toolchain"
cat > "$project/lakefile.lean" <<'EOF'
import Lake
open Lake DSL
package original_sample where
  version := v!"0.1.0"
@[default_target]
lean_lib Sample where
  srcDir := "."
EOF
cat > "$project/Sample.lean" <<'EOF'
namespace Sample
  def inc (x : UInt64) : UInt64 := x + 1
  def twice (x : UInt64) : UInt64 := inc (inc x)
end Sample
#guard Sample.inc 41 == 42
#guard Sample.twice 40 == 42
EOF

out="$tmp/standalone"
bash scripts/compile-project.sh "$project" Sample 'Sample.inc,Sample.twice' \
  "$project/Sample.lean" "$out" > "$tmp/positive.log"
test -s "$out/src/lib.rs"
grep -Fqx 'status=GENERATED_COMPILED_SEMANTICS_NOT_VERIFIED' "$out/receipt.txt"
grep -Fqx 'semantic_verification=NOT_PERFORMED' "$out/receipt.txt"
grep -Fq 'Generated directly from Lean IR declaration: Sample.inc' "$out/src/lib.rs"
grep -Fq 'Generated directly from Lean IR declaration: Sample.twice' "$out/src/lib.rs"
mkdir -p "$out/tests"
cat > "$out/tests/original.rs" <<'EOF'
use lean_generated::{inc, twice};
#[test]
fn checked_original_lean_values() {
    assert_eq!(inc(41_u64), 42);
    assert_eq!(twice(40_u64), 42);
}
EOF
env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
  cargo test --offline --manifest-path "$out/Cargo.toml" > "$tmp/parity.log" 2>&1 || {
  cat "$tmp/parity.log" >&2; exit 1;
}
receipt_hash="$(sha256sum "$out/receipt.txt" | cut -d' ' -f1)"
if bash scripts/compile-project.sh "$project" Sample 'Sample.inc' \
    "$project/Sample.lean" "$out" > "$tmp/overwrite.log" 2>&1; then
  echo "Existing output was overwritten" >&2; exit 1
fi
test "$(sha256sum "$out/receipt.txt" | cut -d' ' -f1)" = "$receipt_hash"
if bash scripts/compile-project.sh "$project" Sample 'Sample.absent' \
    "$project/Sample.lean" "$tmp/refused" > "$tmp/refused.log" 2>&1; then
  echo "Unknown Lean root was accepted" >&2; exit 1
fi
test ! -e "$tmp/refused"
if bash scripts/compile-project.sh "$project" Sample 'Sample.inc]; #eval 0' \
    "$project/Sample.lean" "$tmp/injected" > "$tmp/injected.log" 2>&1; then
  echo "Unsafe root name was accepted" >&2; exit 1
fi
test ! -e "$tmp/injected"
printf 'leanprover/lean4:v4.35.0\n' > "$project/lean-toolchain"
if bash scripts/compile-project.sh "$project" Sample 'Sample.inc' \
    "$project/Sample.lean" "$tmp/wrong-version" > "$tmp/version.log" 2>&1; then
  echo "Wrong project Lean version was accepted" >&2; exit 1
fi
test ! -e "$tmp/wrong-version"
cp "$out/receipt.txt" artifacts/native-project-cli-receipt.txt
echo 'PASS: unchanged imported Lake source, multi-root Cargo, refusals and no-overwrite'
