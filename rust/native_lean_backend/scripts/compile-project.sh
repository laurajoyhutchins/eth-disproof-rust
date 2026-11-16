#!/usr/bin/env bash
# Multi-root native Lean-IR compilation of an unchanged Lake project.
set -euo pipefail
if (( $# != 5 )); then
  echo "usage: compile-project.sh PROJECT_DIR MODULE ROOT[,ROOT...] SOURCE_FILE OUTPUT_DIR" >&2
  exit 2
fi
native="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
source "$native/scripts/lib/compilation-common.sh"
project_arg="$1"; module="$2"; requested="$3"; source_arg="$4"; output_arg="$5"
native_declaration_name "$module" || { echo "Invalid module name" >&2; exit 2; }
IFS=, read -r -a roots <<< "$requested"
(( ${#roots[@]} > 0 )) && [[ "$requested" != ,* && "$requested" != *, && "$requested" != *,,* ]] || {
  echo "Empty root name" >&2; exit 2;
}
for root in "${roots[@]}"; do
  native_declaration_name "$root" || { echo "Invalid root name: $root" >&2; exit 2; }
done
[[ -d "$project_arg" && ! -L "$project_arg" && -f "$source_arg" && ! -L "$source_arg" ]] || {
  echo "Missing project/source or symlink refused" >&2; exit 2;
}
project="$(realpath -e -- "$project_arg")"
source="$(realpath -e -- "$source_arg")"
case "$source" in "$project/"*) ;; *) echo "Source must be inside original project" >&2; exit 2 ;; esac
source_sha_before="$(sha256sum -- "$source" | cut -d' ' -f1)"
[[ ( -f "$project/lakefile.lean" || -f "$project/lakefile.toml" ) && -f "$project/lean-toolchain" ]] || {
  echo "Expected unchanged Lake project (lakefile.lean or lakefile.toml)" >&2; exit 2;
}
[[ "$(cat "$project/lean-toolchain")" == 'leanprover/lean4:v4.34.1' &&
   "$(cat "$native/lean-toolchain")" == 'leanprover/lean4:v4.34.1' ]] || {
  echo "Refusing unpinned Lean project" >&2; exit 2;
}
dest="$(native_destination "$output_arg")"
parent="$(dirname -- "$dest")"
[[ "$(uname -sm)" == 'Linux x86_64' ]] || { echo "Unsupported host ABI" >&2; exit 2; }
: "${LEAN_PREFIX:=$(lean --print-prefix)}"
export PATH="$LEAN_PREFIX/bin:$PATH"
export LD_LIBRARY_PATH="$LEAN_PREFIX/lib/lean${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
[[ "$(lean --version)" == 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)' &&
   "$(rustc --version)" == 'rustc 1.99.1 (58cf8f9c3 2026-10-13)' &&
   -f "$LEAN_PREFIX/include/lean/lean.h" ]] || {
  echo "Lean/Rust/toolchain ABI mismatch" >&2; exit 2;
}
budget="${NATIVE_PROJECT_TIMEOUT_SECONDS:-300}"
[[ "$budget" =~ ^[1-9][0-9]{0,3}$ ]] || { echo "Invalid phase timeout budget" >&2; exit 2; }
mkdir -p "$native/artifacts"
scratch="$(mktemp -d "$native/artifacts/.project-cli.XXXXXXXX")"
publish=''
cleanup() {
  rm -rf -- "$scratch"
  if [[ -n "$publish" ]]; then rm -rf -- "$publish"; fi
}
trap cleanup EXIT

# Only Lake builds the original source. No source rewrite or replacement IR.
(cd "$project" && timeout --signal=TERM --kill-after=5s "${budget}s" lake build "$module") > "$scratch/project.log" 2>&1 || {
  cat "$scratch/project.log" >&2; exit 1;
}
imports="$(cd "$project" && lake env printenv LEAN_PATH)"
[[ -n "$imports" ]] || { echo "Lake import path unavailable" >&2; exit 1; }
export LEAN_PATH="$native:$imports:$LEAN_PREFIX/lib/lean"
(
  cd "$native"
  timeout --signal=TERM --kill-after=5s "${budget}s" cargo build --offline --release
  timeout --signal=TERM --kill-after=5s "${budget}s" lean -o NativeRust.olean NativeRust.lean
) > "$scratch/backend.log" 2>&1 || {
  cat "$scratch/backend.log" >&2; exit 1;
}
plugin="$native/target/release/liblean_rust_native_backend.so"
test -s "$plugin"
joined=''
for root in "${roots[@]}"; do
  if [[ -n "$joined" ]]; then joined="$joined, "; fi
  joined="$joined$root"
done
relative="${scratch#"$native/"}"
printf 'import NativeRust\nimport %s\n#native_rust_package [%s] to "%s/generated"\n' \
  "$module" "$joined" "$relative" > "$scratch/compile.lean"
(
  cd "$native"
  timeout --signal=TERM --kill-after=5s "${budget}s" lean --load-dynlib="$plugin" "$scratch/compile.lean"
) > "$scratch/codegen.log" 2>&1 || {
  cat "$scratch/codegen.log" >&2; exit 1;
}
test -s "$scratch/generated/Cargo.toml"
test -s "$scratch/generated/src/lib.rs"
for root in "${roots[@]}"; do
  grep -Fq "Generated directly from Lean IR declaration: $root" \
    "$scratch/generated/src/lib.rs" || {
    echo "Missing original compiled root: $root" >&2; exit 1;
  }
done
env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
  timeout --signal=TERM --kill-after=5s "${budget}s" cargo test --offline --manifest-path "$scratch/generated/Cargo.toml" \
  > "$scratch/cargo.log" 2>&1 || {
  cat "$scratch/cargo.log" >&2; exit 1;
}
if [[ "$(sha256sum -- "$source" | cut -d' ' -f1)" != "$source_sha_before" ]]; then
  echo "Original source changed while compiling; refusing receipt" >&2; exit 2
fi
publish="$(mktemp -d "$parent/.native-project-publish.XXXXXXXX")"
cp -a -- "$scratch/generated/." "$publish/"
rm -rf -- "$publish/target"
{
  echo 'status=GENERATED_COMPILED_SEMANTICS_NOT_VERIFIED'
  echo "module=$module"
  echo "roots=$requested"
  echo "source_sha256=$source_sha_before"
  echo "phase_timeout_seconds=$budget"
  echo "source_revision=$(git -C "$project" rev-parse HEAD 2>/dev/null || echo unavailable)"
  echo "backend_revision=$(git -C "$native" rev-parse HEAD 2>/dev/null || echo unavailable)"
  echo "lean_version=$(lean --version)"
  echo "rust_version=$(rustc --version)"
  echo "backend_sha256=$(sha256sum "$plugin" | cut -d' ' -f1)"
  echo "generated_sha256=$(sha256sum "$publish/src/lib.rs" | cut -d' ' -f1)"
  echo 'semantic_verification=NOT_PERFORMED'
  echo 'transitive_source_manifest=NOT_CAPTURED'
} > "$publish/receipt.txt"
native_publish_directory "$publish" "$dest" receipt.txt
publish=''
cat "$dest/receipt.txt"
