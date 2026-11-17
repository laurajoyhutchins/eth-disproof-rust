#!/usr/bin/env bash
# Cheap fail-closed admission checks; no network, Mathlib or Lean required.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
bash -n "$HERE/run_pinned.sh"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
git -C "$work" init -q
git -C "$work" -c user.name=GraphCheck -c user.email=graph@example.invalid \
  commit --allow-empty -qm original-source-refusal
for source in openai anthropic; do
  for mode in computation proof all; do
    if bash "$HERE/run_pinned.sh" "$source" "$work" "$work/result" "$mode" \
       > "$work/stdout" 2> "$work/stderr"; then
      echo "An unpinned original source was incorrectly accepted ($source/$mode)" >&2
      exit 1
    fi
    if ! grep -q 'Wrong original source commit' "$work/stderr"; then
      echo "Source pin check was not reached ($source/$mode)" >&2
      cat "$work/stderr" >&2
      exit 1
    fi
  done
done
if bash "$HERE/run_pinned.sh" openai "$work" "$work/result" not-a-mode \
   > "$work/stdout" 2> "$work/stderr"; then
  echo "Invalid extraction mode was incorrectly accepted" >&2
  exit 1
fi
grep -q 'Unknown graph extraction mode' "$work/stderr"
echo "Pinned runner syntactic and source-refusal smoke tests passed"
