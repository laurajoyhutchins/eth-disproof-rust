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
    echo "Unanticipated success for ${root}; add real execution/semantic tests before acceptance" >&2
    exit 1
  fi
  # Reject malformed probes and invalid native oracles: the only permitted
  # error is the native backend's named, precise unsupported refusal.
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
  printf '%s\t%s\t%s\t%s\n' "$root" 'unsupported_explicit' "$metrics" "$log" >> "$manifest"
  rm -f "$target"
done
{
  echo "status=PASS_EXPLICIT_REFUSALS"
  echo "source_revision=$(git rev-parse --verify HEAD 2>/dev/null || echo unavailable)"
  echo "source_identity=Lean_4.34.1_imported_stdlib_at_5045d0056413266e57c625dcd7c365b10e377c52"
  echo "lean_version=$(lean --version)"
  echo "probe_count=3"
  sha256sum examples/ProbeNatGcd.lean examples/ProbeListReverse.lean \
    examples/ProbeStringIntercalate.lean "$manifest" artifacts/imported-probes/*.log
} > artifacts/imported-probes/receipt.txt
cat "$manifest"
cat artifacts/imported-probes/receipt.txt
