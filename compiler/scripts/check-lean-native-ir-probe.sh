#!/usr/bin/env bash
# Narrow, source-faithful comparison. Does not replace the canonical compiler.
set -euo pipefail
cd "$(dirname "$0")/.."

export LEAN_PATH="$PWD:$PWD/examples${LEAN_PATH:+:$LEAN_PATH}"
if [[ -n "${LEAN_PREFIX:-}" ]]; then
  export PATH="$LEAN_PREFIX/bin:$PATH"
  export LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
fi
test "$(cat lean-toolchain)" = "leanprover/lean4:v4.34.1"
lean --version | grep -F "version 4.34.1"
test "$(rustc --version | awk '{print $2}')" = "1.99.1"
command -v cargo >/dev/null
command -v rustfmt >/dev/null
command -v /usr/bin/time >/dev/null

out=artifacts/lean-native-ir-probe
if [[ -e "$out" ]]; then
  echo "Experiment refuses to overwrite its prior output: $out" >&2
  exit 2
fi
mkdir -p "$out"
lean -o LeanNativeRustIR.olean LeanNativeRustIR.lean
cat > "$out/CheckAxioms.lean" <<\x27LEAN\x27
import LeanNativeRustIR
#print axioms LeanNativeRustIR.arithmeticIRRulesSound
LEAN
lean "$out/CheckAxioms.lean" > "$out/axioms.log"
if grep -Fq sorryAx "$out/axioms.log"; then
  echo "Lean-native arithmetic rule theorem depends on sorryAx" >&2
  exit 2
fi
grep -Fq "\x27LeanNativeRustIR.arithmeticIRRulesSound\x27" "$out/axioms.log"
lean -o examples/LeanNativeIRSource.olean examples/LeanNativeIRSource.lean

/usr/bin/time -f 'lean_native_elapsed_s=%e peak_kb=%M' -o "$out/native.time" \
  lean examples/LeanNativeIRFixture.lean > "$out/native.log" 2>&1
for target in arithmetic branches; do
  cargo fmt --all --manifest-path "$out/$target/Cargo.toml"
  cargo fmt --all --check --manifest-path "$out/$target/Cargo.toml"
  cargo test --offline --manifest-path "$out/$target/Cargo.toml" \
    > "$out/$target-tests.log" 2>&1
  cargo clippy --offline --manifest-path "$out/$target/Cargo.toml" \
    --all-targets -- -D warnings > "$out/$target-clippy.log" 2>&1
done

# The same original Lean source is compiled by the existing Rust backend.
cargo build --offline --release
lean -o NativeRust.olean NativeRust.lean
export NATIVE_LIB="$PWD/target/release/liblean_rust_native_backend.so"
/usr/bin/time -f 'rust_backend_elapsed_s=%e peak_kb=%M' -o "$out/existing.time" \
  lean --load-dynlib="$NATIVE_LIB" examples/LeanNativeIRExisting.lean \
    > "$out/existing.log" 2>&1
cargo fmt --all --manifest-path "$out/existing/Cargo.toml"
cargo fmt --all --check --manifest-path "$out/existing/Cargo.toml"
cargo test --offline --manifest-path "$out/existing/Cargo.toml" \
  > "$out/existing-tests.log" 2>&1
cargo clippy --offline --manifest-path "$out/existing/Cargo.toml" \
  --all-targets -- -D warnings > "$out/existing-clippy.log" 2>&1

# A known unsupported original declaration must refuse deterministically.
cat > "$out/Unsupported.lean" <<'LEAN'
import LeanNativeRustIR
def LeanNativeIRUnsupported (s : String) : String := s ++ "x"
#lean_native_ir_package [LeanNativeIRUnsupported]
  to "artifacts/lean-native-ir-probe/unsupported"
LEAN
for attempt in 1 2; do
  if lean "$out/Unsupported.lean" > "$out/refusal-$attempt.log" 2>&1; then
    echo "Unsupported String IR was accepted" >&2
    exit 1
  fi
  grep -Fq '"status":"refused"' "$out/refusal-$attempt.log"
done
cmp "$out/refusal-1.log" "$out/refusal-2.log"
test ! -e "$out/unsupported"

# Determinism is checked on generated Rust, not on formatting/mtime metadata.
sha256sum "$out/arithmetic/src/lib.rs" "$out/branches/src/lib.rs" \
  > "$out/determinism-before.sha256"
rm -rf "$out/arithmetic" "$out/branches"
lean examples/LeanNativeIRFixture.lean > "$out/native-second.log" 2>&1
for target in arithmetic branches; do
  cargo fmt --all --manifest-path "$out/$target/Cargo.toml"
done
sha256sum -c "$out/determinism-before.sha256"

{
  printf 'Lean source: '; sha256sum examples/LeanNativeIRSource.lean
  printf 'Lean emitter: '; sha256sum LeanNativeRustIR.lean
  printf 'Rust existing backend: '; sha256sum backend/src/lib.rs
  printf 'Lean: '; lean --version
  printf 'Rust: '; rustc --version
  printf 'Repository revision: '; git rev-parse HEAD
  printf 'Native generator lines: '; wc -l < LeanNativeRustIR.lean
  printf 'Native output bytes: '; wc -c < "$out/arithmetic/src/lib.rs"
  printf 'Existing output bytes: '; wc -c < "$out/existing/src/lib.rs"
  cat "$out/native.time" "$out/existing.time"
  echo 'Test domains: 49 arithmetic pairs (98 checks) + 49 Bool pairs + 147 existing checks'
  echo 'Proof status: kernel-checked local genuine-IR add/mul emission rules; whole-program Rust refinement open'
} | tee "$out/receipt.txt"
