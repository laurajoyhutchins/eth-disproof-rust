#!/usr/bin/env bash
# #193 item 32: independent, source-pinned, unmodified Lean 4.34.1 projects.
# This is an OBSERVATION run: a precise unsupported declaration is an honest
# outcome, not a successful general-purpose compiler acceptance result.
set -euo pipefail
cd "$(dirname "$0")/.."

: "${LEAN_PREFIX:?Set LEAN_PREFIX to exact Lean 4.34.1 distribution}"
export PATH="${LEAN_PREFIX}/bin:${PATH}"
export LD_LIBRARY_PATH="${LEAN_PREFIX}/lib/lean${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
native="$(pwd)"
plugin="$native/target/release/liblean_rust_native_backend.so"
test -f "$plugin"
test -f "$native/NativeRust.olean"
test "$(cat lean-toolchain)" = "leanprover/lean4:v4.34.1"
test "$(lean --version)" = "Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)"
test -x /usr/bin/time
command -v git >/dev/null
command -v timeout >/dev/null

mkdir -p artifacts/external-projects
out="$native/artifacts/external-projects"
scratch="$(mktemp -d "${TMPDIR:-/tmp}/lean-external-projects.XXXXXXXX")"
trap 'rm -rf -- "$scratch"' EXIT
manifest="$out/manifest.tsv"
printf 'project\tupstream_build\tlean_oracle\tcodegen\tgenerated_rust_build\tcodegen_reason\n' > "$manifest"

# A fixed matrix: no unpinned branches, no user-supplied shell expressions.
# Each is a separate repository and a nontrivial, original executable program.
projects=(
  "newspeak|newspeaklanguage/newspeak|8e8ed029a1d18026eed438103f71e76e5409cc53|formal-semantics/lean|Newspeak.PEG|Newspeak/PEG.lean|Newspeak.ConcreteTree.span"
  "armada|AshishKumar4/armada|c12b4a57bab0c055ab734438249e9510dfc8f970|lean|Sched.Basic|Sched/Basic.lean|Sched.argLeastLoad"
  "keboola|keboola/cli|e29d2cb3385b752c7928e1ea3c7dd9b3cc8d8bcf|formal/sync/lean|SyncModel.Pull|SyncModel/Pull.lean|SyncModel.pullDecide"
)

for spec in "${projects[@]}"; do
  IFS='|' read -r name repository revision subdir module source root <<< "$spec"
  case_dir="$out/$name"
  mkdir -p "$case_dir"
  checkout="$scratch/$name"
  mkdir -p "$checkout"
  git -C "$checkout" init -q
  git -C "$checkout" remote add origin "https://github.com/$repository.git"
  # Sparse, shallow, partial clone limits materialization of large host repos
  # such as keboola/cli; the commit and tree identities remain exact.
  git -C "$checkout" sparse-checkout init --cone
  git -C "$checkout" sparse-checkout set "$subdir"
  if ! timeout 75s git -C "$checkout" -c protocol.version=2 fetch \
      -q --filter=blob:none --depth 1 origin "$revision" > "$case_dir/fetch.log" 2>&1; then
    echo "FATAL: cannot verify immutable upstream source $repository@$revision" >&2
    cat "$case_dir/fetch.log" >&2
    exit 1
  fi
  git -C "$checkout" checkout --detach -q FETCH_HEAD
  actual="$(git -C "$checkout" rev-parse --verify HEAD)"
  if [[ "$actual" != "$revision" ]]; then
    echo "FATAL: fetched wrong source revision for $repository" >&2
    exit 1
  fi
  project="$checkout/$subdir"
  if [[ ! -f "$project/$source" || ! -f "$project/lean-toolchain" ]]; then
    echo "FATAL: upstream pinned module or lean-toolchain missing: $name" >&2
    exit 1
  fi
  if [[ "$(cat "$project/lean-toolchain")" != 'leanprover/lean4:v4.34.1' ]]; then
    echo "FATAL: project toolchain differs from compiler pin: $name" >&2
    exit 1
  fi

  # External source is *never edited*. The separate probes import it by name.
  {
    echo "project=$name"
    echo "repository=$repository"
    echo "upstream_commit=$revision"
    echo "upstream_tree=$(git -C "$checkout" rev-parse 'HEAD^{tree}')"
    echo "module=$module"
    echo "root=$root"
    echo "original_module_sha256=$(sha256sum "$project/$source" | cut -d' ' -f1)"
    echo "original_module_lines=$(wc -l < "$project/$source")"
    echo "source_toolchain=$(cat "$project/lean-toolchain")"
    echo "compiler_revision=$(git rev-parse --verify HEAD 2>/dev/null || echo unavailable)"
    echo "lean_version=$(lean --version)"
    echo "backend_binary_sha256=$(sha256sum "$plugin" | cut -d' ' -f1)"
  } > "$case_dir/identity.txt"

  # Build actual, unchanged module + its genuine upstream dependencies.
  upstream="FAIL"
  oracle="NOT_RUN"
  codegen="NOT_RUN"
  rustbuild="NOT_RUN"
  reason="upstream_compile_failed"
  if (cd "$project" &&
      timeout 120s /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
        -o "$case_dir/upstream.time" lake build "$module") \
        > "$case_dir/upstream.log" 2>&1; then
    upstream="PASS"
    export LEAN_PATH="$native:$project/.lake/build/lib/lean:$LEAN_PREFIX/lib/lean"

    # Original-behavior oracles are kept separate from the codegen process:
    # a failing Lean test must not be confused with a backend refusal.
    case "$name" in
      newspeak)
        guard='#guard decide (Newspeak.ConcreteTree.span (.leaf 2 7) = (2, 7))'
        ;;
      armada)
        guard='#guard decide (Sched.argLeastLoad [3, 1, 4] = 1)'
        ;;
      keboola)
        guard='#guard decide (SyncModel.pullDecide (SyncModel.pSqlEdit true) = .write)'
        ;;
      *) echo "Unknown external acceptance case" >&2; exit 2 ;;
    esac
    printf 'import %s\n%s\n' "$module" "$guard" > "$case_dir/oracle.lean"
    if (cd "$project" && timeout 30s /usr/bin/time \
        -f 'wall_seconds=%e peak_rss_kb=%M' \
        -o "$case_dir/oracle.time" \
        lean "$case_dir/oracle.lean") > "$case_dir/oracle.log" 2>&1; then
      oracle="PASS"
    else
      oracle="FAIL"
      reason="original_lean_oracle_failed"
    fi

    if [[ "$oracle" == 'PASS' ]]; then
      target="$case_dir/generated.rs"
      target_rel="artifacts/external-projects/$name/generated.rs"
      printf '%s\n' 'preserved-existing-output' > "$target"
      cat > "$case_dir/extract.lean" <<LEAN
import NativeRust
import $module
#native_rust_closure $root as "external_root" to "$target_rel"
LEAN
      if (cd "$native" && timeout 45s /usr/bin/time \
          -f 'wall_seconds=%e peak_rss_kb=%M' \
          -o "$case_dir/codegen.time" \
          lean --load-dynlib="$plugin" "$case_dir/extract.lean") \
          > "$case_dir/codegen.log" 2>&1; then
        codegen="GENERATED"
        reason="none"
        if [[ "$(cat "$target")" == 'preserved-existing-output' ]]; then
          echo "FATAL: codegen reported success but did not emit Rust for $name" >&2
          exit 1
        fi
        if timeout 30s /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
           -o "$case_dir/rustbuild.time" \
           rustc --edition=2021 --crate-type lib -D warnings -F unsafe-code \
           "$target" -o "$case_dir/generated.rlib" > "$case_dir/rustbuild.log" 2>&1; then
          rustbuild="PASS"
        else
          rustbuild="FAIL"
          reason="generated_rust_cannot_compile"
        fi
      else
        codegen="REFUSED"
        if ! grep -q 'Rust native backend refused' "$case_dir/codegen.log"; then
          echo "FATAL: unexpected failure is not a precise compiler refusal: $name" >&2
          cat "$case_dir/codegen.log" >&2
          exit 1
        fi
        if [[ "$(cat "$target")" != 'preserved-existing-output' ]]; then
          echo "FATAL: unsupported root mutated prior output: $name" >&2
          exit 1
        fi
        reason="$(grep -m1 'Rust native backend refused' "$case_dir/codegen.log" |
          sed 's/.*Rust native backend refused /refused_/' |
          tr '\t\r\n' '   ' |
          cut -c1-240)"
        rm -f "$target"
      fi
    fi
  fi

  # A successful C/Rust build with no cross-runtime typed adapter is NOT
  # semantic verification. Never upgrade this status implicitly.
  {
    echo "upstream_build=$upstream"
    echo "original_lean_oracle=$oracle"
    echo "native_codegen=$codegen"
    echo "generated_rust_build=$rustbuild"
    echo "generated_rust_semantic_parity=NOT_VERIFIED"
    echo "status=$reason"
    for f in "$case_dir"/*.lean "$case_dir"/*.log "$case_dir"/generated.rs; do
      if [[ -f "$f" ]]; then sha256sum "$f"; fi
    done
  } >> "$case_dir/identity.txt"
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$name" "$upstream" "$oracle" "$codegen" "$rustbuild" "$reason" >> "$manifest"
done

{
  echo "status=COMPLETE_OBSERVATIONS_NOT_G1_ACCEPTANCE"
  echo "source_revision=$(git rev-parse --verify HEAD 2>/dev/null || echo unavailable)"
  echo "tested_external_repositories=3"
  echo "all_upstream_sources_unmodified=true"
  echo "semantic_verification_of_emitted_rust=NOT_ESTABLISHED_UNLESS_SEPARATELY_TESTED"
  echo "toolchain=$(lean --version)"
  sha256sum "$manifest" "$out"/*/identity.txt
} > "$out/receipt.txt"
cat "$manifest"
cat "$out/receipt.txt"
