#!/usr/bin/env bash
# Shared CLI policy; the source-acquisition modes remain deliberately distinct.
native_declaration_name() {
  [[ "$1" =~ ^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$ ]]
}
native_export_name() {
  [[ "$1" =~ ^[A-Za-z_][A-Za-z0-9_]*$ ]]
}
# Resolve a canonical existing parent and refuse existing targets, including
# dangling symlinks. The output basename cannot contain path traversal.
native_destination() {
  local output="$1" basename parent dest
  basename="$(basename -- "$output")"
  if [[ ! "$basename" =~ ^[A-Za-z0-9][A-Za-z0-9_.-]*$ ||
        "$basename" == "." || "$basename" == ".." ]]; then
    echo "Invalid output directory basename: $basename" >&2
    return 2
  fi
  parent="$(realpath -e -- "$(dirname -- "$output")")" || {
    echo "Output parent must already exist" >&2
    return 2
  }
  dest="$parent/$basename"
  if [[ -e "$dest" || -L "$dest" ]]; then
    echo "Refusing destination overwrite: $dest" >&2
    return 2
  fi
  printf '%s\n' "$dest"
}
# GNU mv -n may report success without moving. Verify the staged directory
# disappeared and the receipt arrived at the destination.
native_publish_directory() {
  local staged="$1" destination="$2" receipt="$3"
  [[ -d "$staged" && -f "$staged/$receipt" ]] || {
    echo "Incomplete staged compilation; refusing publication" >&2
    return 2
  }
  mv -Tn -- "$staged" "$destination" || return 2
  if [[ -d "$staged" || ! -f "$destination/$receipt" ]]; then
    echo "Concurrent output collision; no overwrite" >&2
    return 2
  fi
}
