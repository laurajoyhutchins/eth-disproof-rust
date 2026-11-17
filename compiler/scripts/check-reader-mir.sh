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
# Compare the pinned unoptimized MIR operation/branch footprint with the
# *independently certified* original Lean source grammar. These counts are
# deliberately strict: changed MIR printer output requires review instead of
# silently weakening the proof boundary.
if [[ "$opt" == 0 ]]; then
  add_count=$(grep -Fc '>::wrapping_add(' "$function_mir" || true)
  mul_count=$(grep -Fc '>::wrapping_mul(' "$function_mir" || true)
  eq_count=$(grep -Fc ' = Eq(' "$function_mir" || true)
  lt_count=$(grep -Fc ' = Lt(' "$function_mir" || true)
  le_count=$(grep -Fc ' = Le(' "$function_mir" || true)
  bool_count=$(grep -Fc '<u8 as From<bool>>::from(' "$function_mir" || true)
  switch_count=$(grep -Fc 'switchInt(' "$function_mir" || true)
  case "$program" in
    plus)          want=(1 0 0 0 0 0 0) ;;
    straightChain) want=(2 1 0 0 0 0 0) ;;
    choose)        want=(1 1 0 1 0 1 1) ;;
    nested)        want=(1 2 1 0 1 2 2) ;;
  esac
  observed=("$add_count" "$mul_count" "$eq_count" "$lt_count" "$le_count"
            "$bool_count" "$switch_count")
  for n in "${!want[@]}"; do
    if [[ "${observed[$n]}" -ne "${want[$n]}" ]]; then
      echo "MIR audit refused operation/branch footprint drift for $program" >&2
      echo "expected: ${want[*]}; observed: ${observed[*]}" >&2
      exit 2
    fi
  done
  # Every source match is a switch on the 0/1 bool-tag plus an explicit
  # invalid-tag branch. Reject missing alternatives or implicit fallthrough.
  if [[ $switch_count -gt 0 ]]; then
    if [[ $(grep -Ec 'switchInt\(.*\) -> \[0: bb[0-9]+, 1: bb[0-9]+, otherwise: bb[0-9]+\];' "$function_mir" || true) -ne $switch_count ]]; then
      echo "MIR audit refused malformed two-arm Bool tag control flow" >&2
      exit 2
    fi
  fi
  # For choose, cross-check that 1 selects addition and 0 multiplication;
  # tag presence alone would miss reversed control-flow edges.
  if [[ "$program" == "choose" ]]; then
    branch=$(grep -m1 'switchInt(' "$function_mir")
    false_bb=$(printf '%s\n' "$branch" | sed -nE 's/.*\[0: (bb[0-9]+), 1: bb[0-9]+, otherwise:.*/\1/p')
    true_bb=$(printf '%s\n' "$branch" | sed -nE 's/.*\[0: bb[0-9]+, 1: (bb[0-9]+), otherwise:.*/\1/p')
    test -n "$false_bb"
    test -n "$true_bb"
    true_body=$(awk -v block="$true_bb" '
      $0 ~ ("^[[:space:]]*" block ": \\{") {on=1; next}
      on && /^[[:space:]]*}$/ {exit}
      on {print}
    ' "$function_mir")
    false_body=$(awk -v block="$false_bb" '
      $0 ~ ("^[[:space:]]*" block ": \\{") {on=1; next}
      on && /^[[:space:]]*}$/ {exit}
      on {print}
    ' "$function_mir")
    if [[ "$true_body" != *'wrapping_add('* || "$false_body" != *'wrapping_mul('* ]]; then
      echo "MIR audit refused reversed/misrouted Bool control-flow arms" >&2
      exit 2
    fi
  fi
  echo "rustc_mir_footprint=$program:opt0:add$add_count:mul$mul_count:eq$eq_count:lt$lt_count:le$le_count:bool$bool_count:switch$switch_count:PASS"
fi
echo "rustc_mir=${program}:opt${opt}:canonical_function:PASS"
if [[ "$opt" == 0 && ( "$program" == "plus" || "$program" == "choose" ) ]]; then
  echo "=== BEGIN pinned rustc MIR certified_scalar $program opt0 ==="
  sed -n '1,125p' "$function_mir"
  echo "=== END pinned rustc MIR certified_scalar $program opt0 ==="
fi
