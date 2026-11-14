#!/usr/bin/env bash
# Package generated Rust into an independently buildable Cargo library.
# This command does not load or link the Lean runtime.
set -euo pipefail
if (( $# != 3 )); then
  echo "usage: package_crate.sh <generated.rs> <crate_name> <relative_destination>" >&2
  exit 2
fi
source_file="$1"
crate_name="$2"
destination="$3"
if [[ ! "$crate_name" =~ ^[a-z][a-z0-9_]*$ ]]; then
  echo "crate_name must be a lowercase Cargo identifier" >&2; exit 2
fi
if [[ "$destination" = /* || "$destination" = */ || "$destination" = *'//'* || "$destination" = "." ]]; then
  echo "destination must be a simple relative directory path" >&2; exit 2
fi
IFS='/' read -ra components <<< "$destination"
for part in "${components[@]}"; do
  if [[ "$part" == "." || "$part" == ".." || -z "$part" ]]; then
    echo "destination cannot contain traversal components" >&2; exit 2
  fi
done
if [[ ! -f "$source_file" || -L "$source_file" ]]; then
  echo "generated source must be an existing regular file (not a symlink)" >&2; exit 2
fi
if [[ -e "$destination" || -L "$destination" ]]; then
  echo "refusing to overwrite an existing Cargo project" >&2; exit 2
fi
parent="$(dirname -- "$destination")"
if [[ ! -d "$parent" || -L "$parent" ]]; then
  echo "destination parent must be an existing non-symlink directory" >&2; exit 2
fi
cursor="."
for part in "${components[@]:0:${#components[@]}-1}"; do
  cursor="$cursor/$part"
  if [[ -L "$cursor" ]]; then
    echo "destination ancestor is a symlink: $cursor" >&2; exit 2
  fi
done
stage="$(mktemp -d "$parent/.native-cargo-XXXXXXXX")"
trap 'rm -rf -- "$stage"' EXIT
mkdir "$stage/src"
cp -- "$source_file" "$stage/src/lib.rs"
printf '[package]\nname = "%s"\nversion = "0.1.0"\nedition = "2021"\n\n[workspace]\n' "$crate_name" > "$stage/Cargo.toml"
mv -T -- "$stage" "$destination"
trap - EXIT
echo "standalone Cargo library: $destination"
