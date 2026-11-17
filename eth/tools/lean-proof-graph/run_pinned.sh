#!/usr/bin/env bash
set -euo pipefail
[[ $# == 3 ]] || { echo "Usage: $0 openai|anthropic UPSTREAM_REPO OUTPUT_DIR" >&2; exit 2; }
SOURCE=$1; REPO=$(realpath "$2"); OUT=$(realpath -m "$3")
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
case "$SOURCE" in
  openai)
    SHA=7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a
    MATHLIB=d13f23b723b8a846827a245b89c10fc7d3f11612
    VERSION=4.34.1
    # Narrow pinned package, not the unrelated upstream OAI Lake project.
    PROJECT="$HERE/../../../instrumentation/lean-env"
    MODULE=OAI.Algorithms.SubexponentialSAT.Main
    ROOTS=(
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.original_sat_main
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.command
    )
    PREFIXES=(--project-prefix OAI.Algorithms.SubexponentialSAT)
    ;;
  anthropic)
    SHA=16a5ce41304fcdaea4e0be7c132e1c361dc26da5
    MATHLIB=0df444a360eaa60ab8c11dca51a86af692955474
    VERSION=4.33.1
    PROJECT="$REPO/eth"
    MODULE=Solution
    ROOTS=(MainResults.mainTheorem MainResults.ethIsFalse)
    PREFIXES=(--project-prefix MainResults --project-prefix Solution)
    for family in "$PROJECT"/proof/*; do
      [[ -d "$family" ]] || continue
      for directory in "$family"/*; do
        [[ -d "$directory" ]] || continue
        PREFIXES+=(--project-prefix "$(basename "$directory")")
      done
    done
    ;;
  *) echo "Unknown source $SOURCE" >&2; exit 2 ;;
esac
[[ "$(git -C "$REPO" rev-parse HEAD)" == "$SHA" ]] || {
  echo "Wrong original source commit" >&2; exit 1;
}
if [[ "$SOURCE" == openai ]]; then
  ORIG_SRC="$REPO/lean/OAI"
  LINK="$PROJECT/OAI"
  [[ -d "$ORIG_SRC" ]] || { echo "Original OAI source directory absent" >&2; exit 1; }
  if [[ -L "$LINK" ]]; then
    [[ "$(readlink -f "$LINK")" == "$(realpath "$ORIG_SRC")" ]] || {
      echo "OAI source link points at another tree" >&2; exit 1;
    }
  else
    [[ ! -e "$LINK" ]] || { echo "Refusing to overwrite existing OAI path" >&2; exit 1; }
    ln -s "$(realpath "$ORIG_SRC")" "$LINK"
  fi
fi
cd "$PROJECT"
[[ "$(cat lean-toolchain)" == "leanprover/lean4:v$VERSION" ]] || {
  echo "Wrong Lean toolchain pin" >&2; exit 1;
}
lean --version | grep -F "version $VERSION," >/dev/null || {
  echo "Wrong running Lean binary" >&2; exit 1;
}
lake update
[[ "$(git -C .lake/packages/mathlib rev-parse HEAD)" == "$MATHLIB" ]] || {
  echo "Wrong Mathlib source pin" >&2; exit 1;
}
lake build "$MODULE"
lake env lean --run "$HERE/Extract.lean" "$MODULE" "$OUT/$SOURCE.jsonl" "${ROOTS[@]}"
python3 "$HERE/validate.py" "$OUT/$SOURCE.jsonl" \
  --summary "$OUT/$SOURCE-summary.json" \
  --project-view "$OUT/$SOURCE-project-graph.json" \
  --source-sha "$SHA" --mathlib-sha "$MATHLIB" --lean-version "$VERSION" \
  "${PREFIXES[@]}"
