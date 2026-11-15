#!/usr/bin/env bash
# Probe actual imported declarations from the pinned Lean distribution.
# These are NOT three independent real-world Lean projects; their value is
# reproducible coverage gaps without hand-rewriting any algorithms.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LEAN_PREFIX:?Set LEAN_PREFIX to pinned Lean 4.34.1}"
export PATH="${LEAN_PREFIX}/bin:${PATH}"
export LEAN_PATH="$(pwd):${LEAN_PREFIX}/lib/lean${LEAN_PATH:+:${LEAN_PATH}}"
export LD_LIBRARY_PATH="${LEAN_PREFIX}/lib/lean${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
NATIVE_LIB="$(pwd)/target/release/liblean_rust_native_backend.so"
test -f "$NATIVE_LIB"
test -x /usr/bin/time
mkdir -p artifacts/imported-probes
manifest="artifacts/imported-probes/manifest.tsv"
printf 'lean_root\tresult\twall_s_rss_file\tlog\n' > "$manifest"

for pair in 'NatGcd:Nat.gcd' 'ListReverse:List.reverse' 'StringIntercalate:String.intercalate'; do
  fixture="${pair%%:*}"
  root="${pair#*:}"
  target="examples/probe_${fixture}.rs"
  log="artifacts/imported-probes/${fixture}.log"
  metrics="artifacts/imported-probes/${fixture}.time"
  printf 'untouched-output\n' > "$target"
  if /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' -o "$metrics" \
       lean --load-dynlib="$NATIVE_LIB" "examples/Probe${fixture}.lean" > "$log" 2>&1; then
    if [[ "$fixture" != 'ListReverse' ]]; then
      echo "Unexpected native emission for ${root} without source parity tests" >&2
      exit 1
    fi
    if [[ ! -s "$target" || "$(cat "$target")" == 'untouched-output' ]]; then
      echo "Native List.reverse compiler returned success without real Rust" >&2
      exit 1
    fi
    # The new source-erased parameter enables this imported Lean declaration.
    # Treat the change as unverified until the original source's expected
    # outputs are independently evaluated and executed by generated Rust.
    if ! lean examples/ImportedListReverseOracle.lean \
        > "artifacts/imported-probes/ListReverse.oracle.log" 2>&1; then
      cat "artifacts/imported-probes/ListReverse.oracle.log" >&2
      exit 1
    fi
    crate="artifacts/imported-probes/list-reverse-crate"
    mkdir -p "$crate/src"
    cp "$target" "$crate/src/lib.rs"
    cp "artifacts/imported-probes/list-reverse-oracles/source_lean.rs" "$crate/source_lean.rs"
    cat > "$crate/Cargo.toml" <<'TOML'
[package]
name = "lean_imported_list_reverse"
version = "0.1.0"
edition = "2024"
[lib]
path = "src/lib.rs"
[workspace]
TOML
    cat >> "$crate/src/lib.rs" <<'RUST'

#[cfg(test)]
mod source_derived_list_reverse_oracles {
    use super::*;
    include!("../source_lean.rs");
}
RUST
    env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
      cargo test --offline --manifest-path "$crate/Cargo.toml" \
        > "artifacts/imported-probes/ListReverse.cargo.log" 2>&1 || {
      cat "artifacts/imported-probes/ListReverse.cargo.log" >&2
      exit 1
    }
    env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
      cargo test --release --offline --manifest-path "$crate/Cargo.toml" \
        >> "artifacts/imported-probes/ListReverse.cargo.log" 2>&1
    env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
      cargo clippy --offline --manifest-path "$crate/Cargo.toml" \
        --all-targets -- -D warnings >> "artifacts/imported-probes/ListReverse.cargo.log" 2>&1
    printf '%s\t%s\t%s\t%s\n' "$root" '128_original_lean_oracles_PASS' "$metrics" "$log" >> "$manifest"
    continue
  fi
  # Reject malformed probes and invalid native oracles: the only permitted
  # error for the remaining roots is a precise native compiler refusal.
  if [[ "$(grep -c ': error:' "$log" || true)" != 1 ]] || \
     ! grep -q 'error: Rust native backend refused ' "$log"; then
    echo "Probe ${root} failed for reasons other than explicit backend refusal" >&2
    cat "$log" >&2
    exit 1
  fi
  if [[ "$(cat "$target")" != 'untouched-output' ]]; then
    echo "Probe ${root} mutated prior Rust output after refusal" >&2
    exit 1
  fi
  if [[ "$fixture" == 'ListReverse' ]]; then
    echo "List.reverse unexpectedly refused after source-typed proof erasure" >&2
    exit 1
  fi
  printf '%s\t%s\t%s\t%s\n' "$root" 'unsupported_explicit' "$metrics" "$log" >> "$manifest"
  rm -f "$target"
done
{
  echo "status=PASS_ORIGINAL_IMPORT_AND_SOURCE_PARITY"
  echo "source_revision=$(git rev-parse --verify HEAD 2>/dev/null || echo unavailable)"
  echo "source_identity=Lean_4.34.1_imported_stdlib_at_5045d0056413266e57c625dcd7c365b10e377c52"
  echo "lean_version=$(lean --version)"
  echo "probe_count=3"
  echo "list_reverse_original_lean_oracles=128"
  echo "other_imported_probes=2_explicit_refusals"
  sha256sum examples/ProbeNatGcd.lean examples/ProbeListReverse.lean \
    examples/ProbeStringIntercalate.lean examples/ImportedListReverseOracle.lean \
    "$manifest" artifacts/imported-probes/*.log \
    artifacts/imported-probes/list-reverse-crate/src/lib.rs \
    artifacts/imported-probes/list-reverse-crate/source_lean.rs \
    artifacts/imported-probes/list-reverse-crate/Cargo.toml
} > artifacts/imported-probes/receipt.txt
cat "$manifest"
cat artifacts/imported-probes/receipt.txt
