#!/usr/bin/env bash
# Genuine original Lean compiler code -> lungo Bridge IR -> Rust -> parity.
# Stage 0, not a successful self-hosting or semantic-refinement claim.
set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd -P)"
cd "$here"
source "$here/scripts/pins.sh"

: "$LEAN_PREFIX"
test "$(cat "$here/lean/lean-toolchain")" = 'leanprover/lean4:v4.34.1'
test "$( "$LEAN_PREFIX/bin/lean" --version )" = "$BOOTSTRAP_LEAN_VERSION" || {
  echo "Refusing mismatched Lean binary/compiler commit" >&2
  exit 2
}
test "$(rustc --version)" = "$BOOTSTRAP_RUST_VERSION" || {
  echo "Refusing mismatched Rust compiler" >&2
  exit 2
}
mkdir -p "$here/.vendor"
vendor="$here/.vendor/lungo-rs"
if [[ ! -d "$vendor/.git" ]]; then
  if [[ -e "$vendor" || -L "$vendor" ]]; then
    echo "Refusing existing non-Git lungo checkout" >&2
    exit 2
  fi
  git clone --quiet --no-checkout https://github.com/machinefabric/lungo-rs.git "$vendor"
  git -C "$vendor" checkout --quiet --detach "$BOOTSTRAP_LUNGO_SHA"
fi
if [[ "$(git -C "$vendor" rev-parse HEAD)" != "$BOOTSTRAP_LUNGO_SHA" ]] ||
   [[ -n "$(git -C "$vendor" status --porcelain --untracked-files=no)" ]]; then
  echo "Refusing wrong or modified lungo source checkout" >&2
  exit 2
fi

(
  cd "$here/lean"
  lake build Bootstrap
  lake env lean --run Oracle.lean > "$here/oracle.tsv"
)
if [[ "$(wc -l < "$here/oracle.tsv")" -ne 256 ]]; then
  echo "Original Lean oracle did not produce 256 rows" >&2
  exit 1
fi

cargo fmt --manifest-path "$here/Cargo.toml" --all --check
cargo test --manifest-path "$here/Cargo.toml" --all-targets
cargo clippy --manifest-path "$here/Cargo.toml" --all-targets -- -D warnings

mkdir -p "$here/artifacts"
{
  echo 'status=COMPILER_MODULE_EXECUTED_AND_DIFFERENTIALLY_CHECKED'
  echo 'self_hosted=false'
  echo 'lean_rust_refinement_theorem=NOT_ESTABLISHED'
  echo "lean_version=$( "$LEAN_PREFIX/bin/lean" --version )"
  echo "rust_version=$(rustc --version)"
  echo "lungo_revision=$(git -C "$vendor" rev-parse HEAD)"
  echo "source_revision=$(git -C "$here" rev-parse HEAD)"
  echo "oracle_sha256=$(sha256sum "$here/oracle.tsv" | cut -d' ' -f1)"
  echo "fixture_sha256=$(sha256sum "$here/lean/Bootstrap.lean" | cut -d' ' -f1)"
  echo 'upstream_lean_module=Lean.Compiler.IR.Basic'
  echo 'predicates=6'
  echo 'inputs=256'
  echo 'comparisons=1536'
} > "$here/artifacts/receipt.txt"
cat "$here/artifacts/receipt.txt"
