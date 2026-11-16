#!/usr/bin/env bash
# Evidence gate for the actual pinned rustc MIR emitted while linking the
# exact, previously certified Reader-generated Rust function and test driver.
# Stable rustc can emit .mir, but the human-readable MIR printer is unstable.
# This is version-pinned differential evidence, not a formal MIR semantics.
set -euo pipefail
if [[ "$#" -ne 4 ]]; then
  echo "usage: check-reader-mir.sh generated.rs emitted.mir program opt-level" >&2
  exit 2
fi
source=$1
mir=$2
program=$3
opt=$4
case "$program" in
  plus|straightChain|choose|nested) ;;
  *) echo "MIR audit refused unknown program: $program" >&2; exit 2 ;;
esac
case "$opt" in
  0|3) ;;
  *) echo "MIR audit refused optimization level: $opt" >&2; exit 2 ;;
esac
test -s "$source"
test -s "$mir"
# Check the real emitted MIR's top-level function name and argument/return
# signature, without accepting unrelated MIR for the harness main().
if [[ $(grep -Ec '^fn certified_scalar\(' "$mir" || true) -ne 1 ]]; then
  echo "MIR audit requires exactly one canonical certified_scalar" >&2
  exit 2
fi
if ! grep -Eq '^fn certified_scalar\(_1: u64, _2: u64\) -> u64 \{' "$mir"; then
  echo "MIR audit refused unexpected signature / printer drift" >&2
  exit 2
fi
function_mir="${mir%.mir}.function.mir"
awk '
  /^fn certified_scalar\(/ {on=1}
  on {print}
  on && /^}$/ {exit}
' "$mir" > "$function_mir"
test -s "$function_mir"
if ! grep -Eq '^[[:space:]]*bb[0-9]+:' "$function_mir"; then
  echo "MIR audit refused missing basic-block graph" >&2
  exit 2
fi
if ! grep -Fq 'return;' "$function_mir"; then
  echo "MIR audit refused function without return" >&2
  exit 2
fi
if ! grep -Fq 'pub fn certified_scalar(' "$source"; then
  echo "MIR audit refused input without exact certified function" >&2
  exit 2
fi
echo "rustc_mir=${program}:opt${opt}:canonical_function:PASS"
if [[ "$opt" == 0 && ( "$program" == "plus" || "$program" == "choose" ) ]]; then
  echo "=== BEGIN pinned rustc MIR certified_scalar $program opt0 ==="
  sed -n '1,125p' "$function_mir"
  echo "=== END pinned rustc MIR certified_scalar $program opt0 ==="
fi
