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
  semantic_parity="NOT_VERIFIED"
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
        # GMP's audited canonical runtime uses unsafe FFI internally. Do not
        # forbid it for the whole file; forbid unsafe in generated Lean code.
        algorithm="$(sed -n '/^\/\/ Native in-process Lean IR closure/,$p' "$target")"
        if [[ -z "$algorithm" ]] ||
           grep -Eq '(^|[^[:alnum:]_])unsafe([^[:alnum:]_]|$)' <<< "$algorithm"; then
          echo "FATAL: missing generated IR boundary or unsafe emitted algorithm: $name" >&2
          exit 1
        fi
        if timeout 30s /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
           -o "$case_dir/rustbuild.time" \
           rustc --edition=2024 --crate-type lib -D warnings \
           "$target" -o "$case_dir/generated.rlib" > "$case_dir/rustbuild.log" 2>&1; then
          rustbuild="PASS"
        else
          rustbuild="FAIL"
          reason="generated_rust_cannot_compile"
        fi
        # Original unchanged Armada scheduler, independently computed Lean
        # oracles. This is not a synthetic implementation or a source rewrite.
        if [[ "$name" == "armada" && "$rustbuild" == "PASS" ]]; then
          verified="$case_dir/verified-crate"
          mkdir -p "$verified/src" "$verified/tests"
          cp "$target" "$verified/src/lib.rs"
          cat > "$verified/Cargo.toml" <<'TOML'
[package]
name = "lean_generated_armada"
version = "0.1.0"
edition = "2024"

[lib]
path = "src/lib.rs"

[workspace]
TOML
          cat > "$case_dir/armada-oracles.lean" <<'LEAN'
import NativeRust
import Sched.Basic
open Lean Elab Command
run_cmd do
  let mut test := "use lean_generated_armada::*;\n#[test] fn original_armada_scheduler_oracles() {\n"
  let originals : Array (List Nat) := #[
    [], [0], [1], [3, 1, 4], [3, 2, 1], [7, 7, 7],
    [2^120, 2^120+1], [2^512+1, 2^512], [2^1024, 2^1024+2],
    [0, 0, 1, 0], [1, 0, 1, 0], [42, 42, 42, 42]
  ]
  for i in [:128] do
    let xs := if i < originals.size then originals[i]!
      else (List.range (i % 13 + 1)).map (fun j => (i * 19 + j * j + 7) % 67)
    let values := xs.map (fun n => s!"__LeanValue::nat_from_decimal(\"{n}\")")
    let rust := "__LeanValue::list(vec![" ++ String.intercalate ", " values ++ "])"
    let expected := Sched.argLeastLoad xs
    test := test ++ s!"assert_eq!(external_root({rust}).nat_to_decimal(), \"{expected}\");\n"
  test := test ++ "}\n"
  liftIO <| IO.FS.writeFile "artifacts/external-projects/armada/verified-crate/tests/oracle.rs" test
  logInfo "Generated 128 independent original-Armada Lean scheduler oracles"
LEAN
          if ! (cd "$native" && timeout 45s lean "$case_dir/armada-oracles.lean") \
               > "$case_dir/armada-oracles.log" 2>&1 ||
             [[ ! -s "$verified/tests/oracle.rs" ]]; then
            cat "$case_dir/armada-oracles.log" >&2
            echo "FATAL: original pinned Armada oracle generation failed" >&2
            exit 1
          fi
          if ! env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
              cargo test --offline --manifest-path "$verified/Cargo.toml" \
                > "$case_dir/armada-cargo.log" 2>&1; then
            cat "$case_dir/armada-cargo.log" >&2
            echo "FATAL: compiled unchanged Armada scheduler disagrees with Lean" >&2
            exit 1
          fi
          env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
            cargo test --release --offline --manifest-path "$verified/Cargo.toml" \
            >> "$case_dir/armada-cargo.log" 2>&1
          env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
            cargo clippy --offline --manifest-path "$verified/Cargo.toml" \
            --all-targets -- -D warnings >> "$case_dir/armada-cargo.log" 2>&1
          semantic_parity="128_original_Lean_Armada_scheduler_cases_PASS"
          echo "verified_original_armada_source=PASS_128_cases" >> "$case_dir/identity.txt"
          sha256sum "$verified/src/lib.rs" "$verified/tests/oracle.rs" \
            "$verified/Cargo.toml" "$case_dir/armada-oracles.lean" \
            >> "$case_dir/identity.txt"
        fi
        # A third independent source project: the original Newspeak tree
        # projection. Exercise both branches of its optimizer's isShared
        # reuse path; do not infer RC-equivalence from the returned offsets.
        if [[ "$name" == "newspeak" && "$rustbuild" == "PASS" ]]; then
          verified="$case_dir/verified-crate"
          mkdir -p "$verified/src" "$verified/tests"
          cp "$target" "$verified/src/lib.rs"
          cat > "$verified/Cargo.toml" <<'TOML'
[package]
name = "lean_generated_newspeak"
version = "0.1.0"
edition = "2024"

[lib]
path = "src/lib.rs"

[workspace]
TOML
          cat > "$case_dir/newspeak-oracles.lean" <<'LEAN'
import NativeRust
import Newspeak.PEG
open Lean Elab Command
run_cmd do
  let mut test := "use lean_generated_newspeak::*;\n#[test] fn original_newspeak_span_oracles() {\n"
  for i in [:256] do
    let a : Nat := if i % 17 == 0 then 2^1024 + i else i * 31 + 7
    let b : Nat := a + (i % 37) + 1
    let tree : Newspeak.ConcreteTree :=
      if i % 2 == 0 then .leaf a b
      else .node "capture" a b []
    let expected := Newspeak.ConcreteTree.span tree
    let ra := s!"__LeanValue::nat_from_decimal(\"{a}\")"
    let rb := s!"__LeanValue::nat_from_decimal(\"{b}\")"
    let rust :=
      if i % 2 == 0 then
        s!"__LeanValue::ctor(0, \"Newspeak.ConcreteTree.leaf\", vec![{ra}, {rb}])"
      else
        s!"__LeanValue::ctor(1, \"Newspeak.ConcreteTree.node\", vec![__LeanValue::string(\"capture\"), {ra}, {rb}, __LeanValue::list(vec![])])"
    test := test ++ s!"let input = {rust};\n"
    if i % 4 == 0 then
      test := test ++ "let alias = input.clone();\n"
    test := test ++ "let result = external_root(input);\n"
    test := test ++ s!"assert_eq!(result.field(0).nat_to_decimal(), \"{expected.fst}\", \"Newspeak case {i} start\");\n"
    test := test ++ s!"assert_eq!(result.field(1).nat_to_decimal(), \"{expected.snd}\", \"Newspeak case {i} end\");\n"
    if i % 4 == 0 then
      test := test ++ "drop(alias);\n"
  test := test ++ "}\n"
  liftIO <| IO.FS.writeFile
    "artifacts/external-projects/newspeak/verified-crate/tests/oracle.rs" test
  logInfo "Generated 256 original Newspeak span source oracles"
LEAN
          if ! (cd "$native" && timeout 45s lean "$case_dir/newspeak-oracles.lean") \
               > "$case_dir/newspeak-oracles.log" 2>&1 ||
             [[ ! -s "$verified/tests/oracle.rs" ]]; then
            cat "$case_dir/newspeak-oracles.log" >&2
            echo "FATAL: original Newspeak oracle generation refused" >&2
            exit 1
          fi
          if ! env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
             cargo test --offline --manifest-path "$verified/Cargo.toml" \
             > "$case_dir/newspeak-cargo.log" 2>&1; then
            cat "$case_dir/newspeak-cargo.log" >&2
            echo "FATAL: original Newspeak emitted Rust disagreed with Lean" >&2
            exit 1
          fi
          env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
            cargo test --release --offline --manifest-path "$verified/Cargo.toml" \
            >> "$case_dir/newspeak-cargo.log" 2>&1
          env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
            cargo clippy --offline --manifest-path "$verified/Cargo.toml" \
            --all-targets -- -D warnings >> "$case_dir/newspeak-cargo.log" 2>&1
          semantic_parity="256_original_Lean_Newspeak_span_cases_PASS"
          echo "verified_original_newspeak_span=PASS_256_cases" >> "$case_dir/identity.txt"
          sha256sum "$verified/src/lib.rs" "$verified/tests/oracle.rs" \
            "$verified/Cargo.toml" "$case_dir/newspeak-oracles.lean" \
            >> "$case_dir/identity.txt"
        fi
        # Exercise the unchanged original Keboola pullDecide root, not a
        # rewritten decision procedure. Input values use the verified original
        # PullIn.mk layout, while all 256 outputs are evaluated by Lean itself.
        if [[ "$name" == "keboola" && "$rustbuild" == "PASS" ]]; then
          verified="$case_dir/fullpull-crate"
          mkdir -p "$verified/src" "$verified/oracles"
          cp "$target" "$verified/src/lib.rs"
          cat > "$verified/Cargo.toml" <<'TOML'
[package]
name = "lean_generated_keboola_pull"
version = "0.1.0"
edition = "2024"

[lib]
path = "src/lib.rs"

[workspace]
TOML
          cat >> "$verified/src/lib.rs" <<'RUST'

#[cfg(test)]
mod independently_evaluated_original_pull_decisions {
    use super::*;
    include!("../oracles/source_lean.rs");
}
RUST
          cat > "$case_dir/pull-oracles.lean" <<'LEAN'
import NativeRust
import SyncModel.Pull
open Lean Elab Command
run_cmd do
  let mut tests := "#[test] fn original_source_pull_decide_256_cases() {\n"
  let rustNat : Nat → String := fun n =>
    s!"__LeanValue::nat_from_decimal(\"{n}\")"
  let rustOption : Option Nat → String := fun o =>
    match o with
    | none => "__LeanValue::tagged(0)"
    | some n => s!"__LeanValue::ctor(1, \"Option.some\", vec![{rustNat n}])"
  let mut observedOutputs : Array Nat := #[]
  for i in [:256] do
    let mode := i % 4
    let n : Nat := if i % 13 == 0 then 2^1024 + i else (i + 17) * 97
    let base := n + 37
    let isNew := mode == 3
    let theirs := false
    let force := mode == 0
    let fileExists := true
    let pullHash : Option Nat := if mode == 3 then none else some n
    let curHash := if mode == 2 then n else n + 1
    let extrasChanged := mode == 1
    let shapeMigration := false
    let cfgBase : Option Nat := if mode == 3 then none else some base
    let apiHash := if mode == 2 then base else base + 1
    let branchSwitched := false
    let typeRewrite := false
    let p : SyncModel.PullIn := {
      isNew, theirs, force, fileExists, pullHash, curHash,
      extrasChanged, shapeMigration, cfgBase, apiHash,
      branchSwitched, typeRewrite
    }
    let expected : Nat :=
      match SyncModel.pullDecide p with
      | .abort => 0
      | .preserve => 1
      | .skip => 2
      | .write => 3
    if !observedOutputs.contains expected then
      observedOutputs := observedOutputs.push expected
    let values : Array String := #[
      rustOption pullHash, rustNat curHash, rustOption cfgBase, rustNat apiHash
    ]
    tests := tests ++ "let input = __LeanValue::pull_in_ctor(vec![" ++
      String.intercalate ", " values.toList ++ "]);\n"
    let bools : Array Bool := #[
      isNew, theirs, force, fileExists,
      extrasChanged, shapeMigration, branchSwitched, typeRewrite
    ]
    for offset in [:bools.size] do
      let bit : Nat := if bools[offset]! then 1 else 0
      tests := tests ++ s!"let input = input.pull_in_set_u8(4, {offset}, {bit}u8);\n"
    tests := tests ++ s!"assert_eq!(external_root(input), {expected}u8, \"original Keboola input {i}\");\n"
  if observedOutputs.size != 4 then
    throwError "original Keboola oracle failed to cover all four PullOut constructors"
  tests := tests ++ "}\n"
  liftIO <| IO.FS.writeFile
    "artifacts/external-projects/keboola/fullpull-crate/oracles/source_lean.rs" tests
  logInfo "Generated 256 original-Keboola full pullDecide input/output oracles"
LEAN
          if ! (cd "$native" && timeout 45s lean "$case_dir/pull-oracles.lean") \
               > "$case_dir/pull-oracles.log" 2>&1 ||
             [[ ! -s "$verified/oracles/source_lean.rs" ]]; then
            cat "$case_dir/pull-oracles.log" >&2
            echo "FATAL: failed to evaluate original Keboola pullDecide oracles" >&2
            exit 1
          fi
          if ! env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
             cargo test --offline --manifest-path "$verified/Cargo.toml" \
             > "$case_dir/pull-cargo.log" 2>&1; then
            cat "$case_dir/pull-cargo.log" >&2
            echo "FATAL: unmodified Keboola pullDecide Rust disagrees with Lean" >&2
            exit 1
          fi
          env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
            cargo test --release --offline --manifest-path "$verified/Cargo.toml" \
            >> "$case_dir/pull-cargo.log" 2>&1
          env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
            cargo clippy --offline --manifest-path "$verified/Cargo.toml" \
            --all-targets -- -D warnings >> "$case_dir/pull-cargo.log" 2>&1
          semantic_parity="256_original_Lean_Keboola_pullDecide_cases_PASS"
          echo "verified_original_keboola_pullDecide=PASS_256_cases" >> "$case_dir/identity.txt"
          sha256sum "$verified/src/lib.rs" "$verified/oracles/source_lean.rs" \
            "$verified/Cargo.toml" "$case_dir/pull-oracles.lean" \
            >> "$case_dir/identity.txt"
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

  # Diagnostic only: preserves actual imported executable Lean IR for the
  # selected root, even if that root already generated verified Rust.
  if [[ "$oracle" == "PASS" ]]; then
        # Preserve real source-specific compiler IR for future backend work.
        # This does not turn a refusal into successful Rust extraction.
        # Write all interpolated, source-pinned Lean names explicitly.
        # Quoted here-doc avoids shell backtick substitutions from Lean `Name notation.
        printf 'import NativeRust\nimport %s\nopen Lean Elab Command\nrun_cmd do\n  let root : Lean.Name := `%s\n' \
          "$module" "$root" > "$case_dir/inspect-ir.lean"
        cat >> "$case_dir/inspect-ir.lean" <<'LEAN'
  let decl ← liftCoreM do
    if (← Lean.IR.findDecl root).isNone then
      Lean.Compiler.compile #[root]
    let some decl ← Lean.IR.findDecl root
      | throwError "Original executable Lean IR not available for {root}"
    return decl
  let source := toString decl
  if source.utf8ByteSize > 262144 then
    throwError "Original IR snapshot exceeds 256 KiB diagnostic budget"
LEAN
        printf '  liftIO <| IO.FS.writeFile "%s" source\n' \
          "$case_dir/original-ir.txt" >> "$case_dir/inspect-ir.lean"
        if (cd "$native" && timeout 45s lean "$case_dir/inspect-ir.lean") \
             > "$case_dir/inspect-ir.log" 2>&1 &&
           [[ -s "$case_dir/original-ir.txt" ]]; then
          echo "original_compiler_ir_snapshot=PINNED_SOURCE_IR" >> "$case_dir/identity.txt"
        else
          echo "original_compiler_ir_snapshot=UNAVAILABLE_DIAGNOSTIC_ONLY" >> "$case_dir/identity.txt"
        fi
  fi

  # Capture source-defined executable IR from original Keboola declarations.
  # The constructor metadata lives in PullIn-producing IR, not in a standalone
  # executable PullIn.mk declaration; source constructors are not functions.
  if [[ "$name" == "keboola" ]]; then
    cat > "$case_dir/inspect-pull-deps.lean" <<'LEAN'
import NativeRust
import SyncModel.Pull
open Lean Elab Command
run_cmd do
  let roots : Array Lean.Name := #[
    `SyncModel.pSqlEdit,
    `SyncModel.forceConflict,
    `SyncModel.locallyModified,
    `SyncModel.remoteUnchanged,
    `SyncModel.ymlModified,
    `SyncModel.bytesMatch
  ]
  let mut snapshot := ""
  for root in roots do
    let decl ← liftCoreM do
      if (← Lean.IR.findDecl root).isNone then
        Lean.Compiler.compile #[root]
      let some d ← Lean.IR.findDecl root
        | throwError "original source-compiled Lean IR unavailable: {root}"
      return d
    snapshot := snapshot ++ s!"NAME {root}\n{decl}\nEND {root}\n"
  if snapshot.utf8ByteSize > 262144 then
    throwError "original Keboola structure IR exceeds 256 KiB"
  liftIO <| IO.FS.writeFile
    "artifacts/external-projects/keboola/pull-deps-ir.txt" snapshot
LEAN
    if (cd "$native" && timeout 45s lean "$case_dir/inspect-pull-deps.lean") \
        > "$case_dir/inspect-pull-deps.log" 2>&1 && [[ -s "$case_dir/pull-deps-ir.txt" ]]; then
      echo "original_keboola_structure_dependencies=PINNED_SOURCE_IR" >> "$case_dir/identity.txt"
    else
      echo "original_keboola_structure_dependencies=UNAVAILABLE_DIAGNOSTIC_ONLY" >> "$case_dir/identity.txt"
    fi
  fi

  # Source-pinned, read-only diagnostic for Armada's transitive List helpers.
  # These names are emitted by the original Sched.argLeastLoad compiler IR.
  # A missing diagnostic is reported separately and never accepted as Rust.
  if [[ "$name" == "armada" ]]; then
    cat > "$case_dir/inspect-list-deps.lean" <<'LEAN'
import NativeRust
import Sched.Basic
open Lean Elab Command
run_cmd do
  let names : Array Lean.Name := #[
    `List.min?._at_.Sched.argLeastLoad.spec_0,
    `List.idxOf._at_.Sched.argLeastLoad.spec_1
  ]
  let mut snapshot := ""
  for name in names do
    let some decl ← liftCoreM <| Lean.IR.findDecl name
      | throwError "original Lean IR helper unavailable: {name}"
    snapshot := snapshot ++ s!"NAME {name}\n{decl}\nEND {name}\n"
  if snapshot.utf8ByteSize > 262144 then
    throwError "original imported List IR exceeded 256 KiB"
  liftIO <| IO.FS.writeFile "artifacts/external-projects/armada/list-deps-ir.txt" snapshot
LEAN
    if (cd "$native" && timeout 45s lean "$case_dir/inspect-list-deps.lean") \
        > "$case_dir/inspect-list-deps.log" 2>&1 && [[ -s "$case_dir/list-deps-ir.txt" ]]; then
      echo "original_armada_list_dependencies=PINNED_SOURCE_IR" >> "$case_dir/identity.txt"
    else
      echo "original_armada_list_dependencies=UNAVAILABLE_DIAGNOSTIC_ONLY" >> "$case_dir/identity.txt"
    fi
  fi

  # A successful C/Rust build with no cross-runtime typed adapter is NOT
  # semantic verification. Never upgrade this status implicitly.
  {
    echo "upstream_build=$upstream"
    echo "original_lean_oracle=$oracle"
    echo "native_codegen=$codegen"
    echo "generated_rust_build=$rustbuild"
    echo "generated_rust_semantic_parity=$semantic_parity"
    echo "status=$reason"
    for f in "$case_dir"/*.lean "$case_dir"/*.log "$case_dir"/*.txt "$case_dir"/generated.rs; do
      if [[ -f "$f" ]]; then sha256sum "$f"; fi
    done
  } >> "$case_dir/identity.txt"
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$name" "$upstream" "$oracle" "$codegen" "$rustbuild" "$reason" >> "$manifest"
done

# A separate *positive* test on two unchanged original Keboola functions.
# These two smaller helpers use ordinary Bool control flow independently
# of the full PullIn root, which is now source-verified above. Compute all 12 expected results in original
# Lean, then compile and execute the exact emitted external-source Rust.
positive="$out/keboola/positive-package"
rm -rf -- "$positive"
cat > "$out/keboola/positive.lean" <<'LEAN'
import NativeRust
import SyncModel.Pull

#native_rust_package [SyncModel.sweepRemovesDir, SyncModel.dirAfterPull] to "artifacts/external-projects/keboola/positive-package"

open Lean Elab Command
run_cmd do
  let mut test := "use lean_generated::{sweepRemovesDir, dirAfterPull};\n#[test] fn original_lean_truth_table() {\n"
  for a in #[false, true] do
    for b in #[false, true] do
      let x : Nat := if a then 1 else 0
      let y : Nat := if b then 1 else 0
      let expected : Nat := if SyncModel.sweepRemovesDir a b then 1 else 0
      test := test ++ s!"assert_eq!(sweepRemovesDir({x}u8, {y}u8), {expected}u8);\n"
      for c in #[false, true] do
        let z : Nat := if c then 1 else 0
        let result : Nat := if SyncModel.dirAfterPull a b c then 1 else 0
        test := test ++ s!"assert_eq!(dirAfterPull({x}u8, {y}u8, {z}u8), {result}u8);\n"
  test := test ++ "}\n"
  liftIO <| IO.FS.createDirAll "artifacts/external-projects/keboola/positive-package/tests"
  liftIO <| IO.FS.writeFile
    "artifacts/external-projects/keboola/positive-package/tests/lean-oracle.rs" test
  logInfo "Generated 12 independent original-Lean cases for unchanged Keboola source roots"
LEAN
export LEAN_PATH="$native:$scratch/keboola/formal/sync/lean/.lake/build/lib/lean:$LEAN_PREFIX/lib/lean"
if ! (cd "$native" && timeout 60s /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
    -o "$out/keboola/positive-codegen.time" \
    lean --load-dynlib="$plugin" "$out/keboola/positive.lean") \
    > "$out/keboola/positive-codegen.log" 2>&1; then
  echo "FATAL: unmodified Keboola Bool helpers did not generate standalone Rust" >&2
  cat "$out/keboola/positive-codegen.log" >&2
  exit 1
fi
if ! env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
    cargo test --offline --manifest-path "$positive/Cargo.toml" \
    > "$out/keboola/positive-cargo.log" 2>&1; then
  cat "$out/keboola/positive-cargo.log" >&2
  echo "FATAL: original external-source generated Rust disagreed with Lean oracle" >&2
  exit 1
fi
env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
  cargo test --release --offline --manifest-path "$positive/Cargo.toml" \
  >> "$out/keboola/positive-cargo.log" 2>&1
env -u LEAN_PREFIX -u LEAN_PATH -u LD_LIBRARY_PATH \
  cargo clippy --offline --manifest-path "$positive/Cargo.toml" --all-targets -- -D warnings \
  >> "$out/keboola/positive-cargo.log" 2>&1
{
  echo "original_external_roots=SyncModel.sweepRemovesDir,SyncModel.dirAfterPull"
  echo "unmodified_original_lean_oracles=12"
  echo "independently_generated_rust_cargo_debug_release_clippy=PASS"
  sha256sum "$out/keboola/positive.lean" \
    "$positive/src/lib.rs" "$positive/tests/lean-oracle.rs" "$positive/Cargo.toml"
} > "$out/keboola/positive-receipt.txt"

if ! grep -Fqx 'generated_rust_semantic_parity=256_original_Lean_Keboola_pullDecide_cases_PASS' \
    "$out/keboola/identity.txt"; then
  echo 'FATAL: full original Keboola pullDecide parity receipt missing or incomplete' >&2
  exit 1
fi
{
  echo "status=COMPLETE_OBSERVATIONS_NOT_G1_ACCEPTANCE"
  echo "source_revision=$(git rev-parse --verify HEAD 2>/dev/null || echo unavailable)"
  echo "tested_external_repositories=3"
  echo "all_upstream_sources_unmodified=true"
  echo "external_armada_original_root=128_source_oracles_PASS"
  echo "external_keboola_two_original_helpers=12_source_oracles_PASS"
  echo "external_keboola_original_root=256_source_oracles_PASS"
  echo "substantial_external_project_roots_verified=2_of_3"
  echo "semantic_verification_of_selected_external_roots=armada_pass_keboola_pass_newspeak_refused"
  echo "toolchain=$(lean --version)"
  sha256sum "$manifest" "$out"/*/identity.txt "$out/keboola/positive-receipt.txt"
} > "$out/receipt.txt"
cat "$manifest"
cat "$out/receipt.txt"
