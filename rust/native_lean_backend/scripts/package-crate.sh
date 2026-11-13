#!/usr/bin/env bash
set -euo pipefail
if [[ $# != 3 ]]; then
  echo "usage: package-crate.sh <generated.rs> <new-output-dir> <crate-name>" >&2
  exit 2
fi
source_file="$1"
destination="$2"
crate_name="$3"
if [[ ! -f "$source_file" ]] || [[ ! "$crate_name" =~ ^[a-z][a-z0-9_]*$ ]]; then
  echo "source must exist and crate name must be a lowercase Rust identifier" >&2
  exit 2
fi
if [[ -e "$destination" || -L "$destination" ]]; then
  echo "refusing to overwrite existing crate directory: $destination" >&2
  exit 2
fi
parent="$(dirname "$destination")"
if [[ ! -d "$parent" ]]; then
  echo "crate parent directory does not exist: $parent" >&2
  exit 2
fi
# Stage all files in the destination filesystem and publish with one rename.
stage="$(mktemp -d "$parent/.native-lean-crate.XXXXXXXX")"
trap 'rm -rf "$stage"' EXIT
mkdir "$stage/src"
cp "$source_file" "$stage/src/lib.rs"
cat > "$stage/Cargo.toml" <<TOML
[package]
name = "$crate_name"
version = "0.1.0"
edition = "2021"

[lib]
path = "src/lib.rs"

[workspace]
TOML
# The target must not exist. Never use mv's implicit merge or replacement mode.
if [[ -e "$destination" || -L "$destination" ]]; then
  echo "crate destination appeared during staging" >&2
  exit 2
fi
mv -T "$stage" "$destination"
trap - EXIT
