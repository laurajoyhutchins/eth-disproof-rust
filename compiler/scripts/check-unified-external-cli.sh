#!/usr/bin/env bash
# Execute the three unmodified upstream projects through the *public*
# eth-compiler interface, not only through the native FFI smoke harness.
# The third substantial-program gate still requires a larger Newspeak root.
set -euo pipefail

: "${EXTERNAL_SOURCE_CHECKOUTS:?Unmodified, pinned external Git checkouts required}"
: "${EXTERNAL_EVIDENCE_DIR:?Existing independent Lean oracle evidence required}"
: "${EXTERNAL_NATIVE_ROOT:?Canonical native G1 backend required}"
: "${LEAN_PREFIX:?Pinned Lean 4.34.1 required}"

native="$(realpath -e "$EXTERNAL_NATIVE_ROOT")"
workspace="$(realpath -e "$native/..")"
scratch="$(realpath -e "$EXTERNAL_SOURCE_CHECKOUTS")"
out="$(realpath -e "$EXTERNAL_EVIDENCE_DIR")"
test -f "$workspace/Cargo.toml"
test -f "$workspace/Cargo.lock"
test "$(cat "$native/lean-toolchain")" = 'leanprover/lean4:v4.34.1'
test "$(lean --version)" = 'Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)'

# All three roots already have independently evaluated original Lean outputs,
# compiled from exact public upstream commits by check-external-projects.sh.
# The target being *substantial* is a separate, explicit acceptance property.
specs=(
  'armada|AshishKumar4/armada|c12b4a57bab0c055ab734438249e9510dfc8f970|lean|Sched.Basic|Sched/Basic.lean|Sched.argLeastLoad|argLeastLoad|128|yes'
  'keboola|keboola/cli|e29d2cb3385b752c7928e1ea3c7dd9b3cc8d8bcf|formal/sync/lean|SyncModel.Pull|SyncModel/Pull.lean|SyncModel.pullDecide|pullDecide|256|yes'
  'newspeak|newspeaklanguage/newspeak|8e8ed029a1d18026eed438103f71e76e5409cc53|formal-semantics/lean|Newspeak.PEG|Newspeak/PEG.lean|Newspeak.ConcreteTree.span|span|256|no'
)

summary="$out/unified-cli-manifest.tsv"
printf 'project\tupstream_commit\troot\toriginal_lean_cases\tcompiled_with_eth_compiler\tstandalone_parity\tsubstantial_root\n' > "$summary"

for spec in "${specs[@]}"; do
  IFS='|' read -r name repository revision subdir module source root public cases substantial <<< "$spec"
  checkout="$scratch/$name"
  project="$checkout/$subdir"
  source_file="$project/$source"
  case_dir="$out/$name"
  package="$case_dir/unified-cli-package"
  receipt="$case_dir/unified-cli.receipt.json"
  oracle_package="$case_dir/unified-cli-oracle-package"

  test "$(git -C "$checkout" rev-parse HEAD)" = "$revision"
  test -f "$source_file"
  test -f "$project/lean-toolchain"
  test "$(cat "$project/lean-toolchain")" = 'leanprover/lean4:v4.34.1'
  test -f "$case_dir/identity.txt"
  grep -Fqx 'upstream_build=PASS' "$case_dir/identity.txt"
  grep -Fqx 'native_codegen=GENERATED' "$case_dir/identity.txt"
  grep -Fqx 'generated_rust_build=PASS' "$case_dir/identity.txt"
  case "$name" in
    armada)
      grep -Fqx 'generated_rust_semantic_parity=128_original_Lean_Armada_scheduler_cases_PASS' "$case_dir/identity.txt"
      oracle="$case_dir/verified-crate/tests/oracle.rs"
      ;;
    keboola)
      grep -Fqx 'generated_rust_semantic_parity=256_original_Lean_Keboola_pullDecide_cases_PASS' "$case_dir/identity.txt"
      oracle="$case_dir/fullpull-crate/oracles/source_lean.rs"
      ;;
    newspeak)
      grep -Fqx 'generated_rust_semantic_parity=256_original_Lean_Newspeak_span_cases_PASS' "$case_dir/identity.txt"
      oracle="$case_dir/verified-crate/oracles/source_lean.rs"
      ;;
    *) echo "Unrecognized pinned project" >&2; exit 2 ;;
  esac
  test -s "$oracle"
  test ! -e "$package"
  test ! -e "$receipt"
  test ! -e "$oracle_package"

  # Public compiler invocation, as an end-user would run it on the unchanged
  # project; source identity is read from *its own* Git tree, not our checkout.
  /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
    -o "$case_dir/unified-cli.time" \
    cargo run --locked --offline --manifest-path "$workspace/Cargo.toml" \
      -p lean-eth-reference --bin eth-compiler -- compile \
      --backend compiler-ir \
      --source-repo "$checkout" --source-revision "$revision" \
      --source-path "$subdir/$source" \
      --source-toolchain-path "$subdir/lean-toolchain" \
      --lake-root "$project" \
      --module "$module" --root "$root" \
      --timeout-seconds 300 \
      --output "$package" --receipt "$receipt" \
      > "$case_dir/unified-cli.log" 2>&1 || {
    cat "$case_dir/unified-cli.log" >&2
    echo "FATAL: public compiler failed unchanged upstream $repository@$revision" >&2
    exit 1
  }

  cargo run --locked --offline --manifest-path "$workspace/Cargo.toml" \
      -p lean-eth-reference --bin eth-compiler -- verify \
      --backend compiler-ir \
      --source-repo "$checkout" --source-revision "$revision" \
      --source-path "$subdir/$source" \
      --source-toolchain-path "$subdir/lean-toolchain" \
      --module "$module" --root "$root" \
      --artifact "$package" --receipt "$receipt" \
      >> "$case_dir/unified-cli.log" 2>&1

  test -s "$package/src/lib.rs"
  test -s "$package/Cargo.toml"
  test -s "$package/receipt.txt"
  grep -Fq "Generated directly from Lean IR declaration: $root" "$package/src/lib.rs"
  jq -e --arg root "$root" --arg rev "$revision" '
    .backend == "compiler-ir"
    and .status == "generated-unverified"
    and .roots == [$root]
    and .source_file.git_revision == $rev
    and .backend_report.source_revision == $rev
    and .backend_report.compiler == "native-lean-4.34.1"
    and .executable_approved == false
    and .checks.lean_rust_semantic_refinement == "not-established"
  ' "$receipt" > /dev/null

  # Compile and run the very same emitted source with original Lean oracles.
  # The accepted generated package is never modified; only a test-only copy
  # receives oracle sources. Check core source bytes before adding tests.
  cp -a -- "$package" "$oracle_package"
  cmp "$package/src/lib.rs" "$oracle_package/src/lib.rs"
  if [[ "$name" == armada ]]; then
    mkdir -p "$oracle_package/tests"
    sed -e 's/lean_generated_armada/lean_generated/g' \
        -e "s/external_root(/$public(/g" "$oracle" \
        > "$oracle_package/tests/source_lean.rs"
  else
    mkdir -p "$oracle_package/oracles"
    sed "s/external_root(/$public(/g" "$oracle" \
        > "$oracle_package/oracles/source_lean.rs"
    cat >> "$oracle_package/src/lib.rs" <<'RUST'

#[cfg(test)]
mod original_lean_source_oracles {
    use super::*;
    include!("../oracles/source_lean.rs");
}
RUST
  fi

  # Rust generated code and the source-derived Lean oracle tests are the
  # only algorithm inputs; no standalone Lean runtime is present at execution.
  env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
    cargo test --locked --offline --manifest-path "$oracle_package/Cargo.toml" \
    > "$case_dir/unified-oracle-cargo.log" 2>&1 || {
    cat "$case_dir/unified-oracle-cargo.log" >&2
    echo "FATAL: unified compiler differs from original $name Lean oracle" >&2
    exit 1
  }
  env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
    cargo test --locked --release --offline --manifest-path "$oracle_package/Cargo.toml" \
    >> "$case_dir/unified-oracle-cargo.log" 2>&1
  env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
    cargo clippy --locked --offline --manifest-path "$oracle_package/Cargo.toml" \
      --all-targets -- -D warnings >> "$case_dir/unified-oracle-cargo.log" 2>&1

  # Independent, reproducible evidence is per source/project and never
  # substitutes the 256 Newspeak span cases for the larger PEG checker.
  {
    echo "status=UNIFIED_COMPILER_ORIGINAL_LEAN_ORACLE_PARITY"
    echo "upstream_repository=$repository"
    echo "upstream_revision=$revision"
    echo "original_source=$subdir/$source"
    echo "module=$module"
    echo "root=$root"
    echo "independent_lean_oracle_cases=$cases"
    echo "substantial_project_root=$substantial"
    echo "native_backend=in_process_Lean_4.34.1_IR_to_Rust"
    echo "semantic_coverage=FINITE_ORACLES_NOT_A_PROOF"
    echo "transitive_source_manifest=NOT_CAPTURED"
    sha256sum "$source_file" "$oracle" "$package/src/lib.rs" \
      "$package/Cargo.toml" "$package/receipt.txt" "$receipt"
    if [[ "$name" == armada ]]; then
      sha256sum "$oracle_package/tests/source_lean.rs"
    else
      sha256sum "$oracle_package/oracles/source_lean.rs"
    fi
  } > "$case_dir/unified-cli-evidence.txt"
  printf '%s\t%s\t%s\t%s\tPASS\tPASS\t%s\n' \
    "$name" "$revision" "$root" "$cases" "$substantial" >> "$summary"
done

grep -Fqx $'armada\tc12b4a57bab0c055ab734438249e9510dfc8f970\tSched.argLeastLoad\t128\tPASS\tPASS\tyes' "$summary"
grep -Fqx $'keboola\te29d2cb3385b752c7928e1ea3c7dd9b3cc8d8bcf\tSyncModel.pullDecide\t256\tPASS\tPASS\tyes' "$summary"
grep -Fqx $'newspeak\t8e8ed029a1d18026eed438103f71e76e5409cc53\tNewspeak.ConcreteTree.span\t256\tPASS\tPASS\tno' "$summary"
printf '%s\n' \
  'status=THREE_UPSTREAM_PROJECTS_PUBLIC_CLI_TWO_SUBSTANTIAL_ROOTS' \
  'original_external_projects_with_unified_cli=3' \
  'substantial_external_project_roots_verified=2_of_3' \
  'newspeak_certificate_status=NOT_ACCEPTED' \
  'G1_item_53=OPEN' > "$out/unified-cli-summary.txt"
sha256sum "$summary" >> "$out/unified-cli-summary.txt"
cat "$summary"
cat "$out/unified-cli-summary.txt"
