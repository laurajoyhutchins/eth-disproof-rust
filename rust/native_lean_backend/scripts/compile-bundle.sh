#!/usr/bin/env bash
# Reproducible, content-addressable evidence around the existing in-process
# compiler. A bundle is an ATOMIC DIRECTORY publication (not paired file writes).
# Generated code is only COMPILE-verified here; semantic acceptance is separate.
set -euo pipefail
cd "$(dirname "$0")/.."

if (( $# < 4 || $# > 5 )); then
  echo "usage: compile-bundle.sh MODULE ROOT SOURCE_LEAN OUTPUT_DIRECTORY [RUST_EXPORT]" >&2
  exit 2
fi
module="$1"
root="$2"
source="$3"
dest="$4"
export_name="${5:-compiled_root}"

# Lean names are inserted into a compiler command, never passed to a shell eval.
# Restrict the first public CLI to ordinary ASCII components.
name_re='^[a-zA-Z_][a-zA-Z0-9_]*(\.[a-zA-Z_][a-zA-Z0-9_]*)*$'
export_re='^[a-zA-Z_][a-zA-Z0-9_]*$'
if ! [[ "$module" =~ $name_re && "$root" =~ $name_re && "$export_name" =~ $export_re ]]; then
  echo "Refusing unsafe Lean module/root or Rust export name" >&2
  exit 2
fi
if [[ ! -f "$source" || -L "$source" || "$dest" = *'/../'* || "$dest" = '../'* ]]; then
  echo "Refusing missing/symlinked source or traversal in output path" >&2
  exit 2
fi
filename="$(basename -- "$dest")"
if ! [[ "$filename" =~ ^[a-zA-Z0-9][a-zA-Z0-9_.-]*$ ]] ||
    [[ "$filename" = '.' || "$filename" = '..' ]]; then
  echo "Refusing unsafe bundle directory name" >&2
  exit 2
fi
: "${LEAN_PREFIX:?Set LEAN_PREFIX to exact Lean 4.34.1 distribution}"
export PATH="${LEAN_PREFIX}/bin:${PATH}"
export LEAN_PATH="$(pwd):$(pwd)/examples:${LEAN_PREFIX}/lib/lean${LEAN_PATH:+:${LEAN_PATH}}"
export LD_LIBRARY_PATH="${LEAN_PREFIX}/lib/lean${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
if [[ "$(lean --version)" != *'version 4.34.1'* ]] ||
   [[ "$(rustc --version)" != 'rustc 1.99.1 '* ]]; then
  echo "Unsupported toolchain; this bundle requires Lean 4.34.1 and Rust 1.99.1" >&2
  exit 2
fi
NATIVE_LIB="$(pwd)/target/release/liblean_rust_native_backend.so"
test -f "$NATIVE_LIB"
test -f NativeRust.olean

parent="$(realpath -e -- "$(dirname -- "$dest")")"
dest="$parent/$filename"
if [[ -e "$dest" || -L "$dest" ]]; then
  echo "Refusing to overwrite existing bundle: $dest" >&2
  exit 2
fi
staging="$(mktemp -d "$parent/.native-bundle.XXXXXXXX")"
# Never remove a caller's destination even on any error.
trap 'rm -rf -- "$staging"' EXIT
if [[ "$staging" = *'"'* || "$staging" = *'\'* || "$staging" = *$'\n'* ]]; then
  echo "Bundle parent cannot contain Lean string escape characters" >&2
  exit 2
fi

module_file="${module//.//}"
mkdir -p -- "$staging/$(dirname "$module_file")"
cp -- "$source" "$staging/$module_file.lean"
export LEAN_PATH="$staging:$LEAN_PATH"
if ! lean -o "$staging/$module_file.olean" "$staging/$module_file.lean" > "$staging/lean-module.log" 2>&1; then
  cat "$staging/lean-module.log" >&2
  exit 1
fi
cat > "$staging/compile.lean" <<LEAN
import NativeRust
import $module
#native_rust_closure $root as "$export_name" to "$staging/generated.rs"
LEAN
if ! lean --load-dynlib="$NATIVE_LIB" "$staging/compile.lean" > "$staging/lean-codegen.log" 2>&1; then
  cat "$staging/lean-codegen.log" >&2
  exit 1
fi
test -s "$staging/generated.rs"

# This is a standalone Rust library compilation check; not a semantic proof.
if ! rustc --edition=2021 --crate-type=lib -D warnings -F unsafe-code \
    -o "$staging/libgenerated.rlib" "$staging/generated.rs" > "$staging/rust-build.log" 2>&1; then
  cat "$staging/rust-build.log" >&2
  exit 1
fi
sed -n 's@^// Generated directly from Lean IR declaration: @@p' \
  "$staging/generated.rs" | LC_ALL=C sort -u > "$staging/closure.txt"
if [[ ! -s "$staging/closure.txt" ]] || ! grep -Fxq "$root" "$staging/closure.txt"; then
  echo "Generated code lacks the root declaration's closure provenance" >&2
  exit 1
fi

hash() { sha256sum -- "$1" | cut -d' ' -f1; }
{
  echo "status=GENERATED_COMPILED_UNVERIFIED"
  echo "source_revision=$(git rev-parse --verify HEAD 2>/dev/null || echo unavailable)"
  echo "source_module=$module"
  echo "root_declaration=$root"
  echo "rust_export=$export_name"
  echo "lean_toolchain=$(cat lean-toolchain)"
  echo "lean_version=$(lean --version)"
  echo "rust_version=$(rustc --version)"
  echo "source_lean_sha256=$(hash "$staging/$module_file.lean")"
  echo "compiled_olean_sha256=$(hash "$staging/$module_file.olean")"
  echo "native_abi_sha256=$(hash native/abi.c)"
  echo "native_backend_sha256=$(hash src/lib.rs)"
  echo "native_shared_library_sha256=$(hash "$NATIVE_LIB")"
  echo "closure_names_sha256=$(hash "$staging/closure.txt")"
  echo "generated_rust_sha256=$(hash "$staging/generated.rs")"
  echo "generated_rlib_sha256=$(hash "$staging/libgenerated.rlib")"
  echo "lean_source_status=source_hash_pinned_but_transitive_imports_not_fully_hashed"
  echo "semantic_verification=NOT_PERFORMED"
  echo "execution_runtime=standalone_rust_lib_without_lean"
} > "$staging/receipt.txt"

# Move the entire bundle as one unit, including generated source and receipt.
# GNU -n may report success without actually moving; assert staged dir gone.
mv -Tn -- "$staging" "$dest"
if [[ -d "$staging" || ! -f "$dest/receipt.txt" ]]; then
  echo "Output directory appeared concurrently; no bundle overwritten" >&2
  exit 2
fi
trap - EXIT
cat "$dest/receipt.txt"
