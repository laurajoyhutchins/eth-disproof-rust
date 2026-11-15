#!/usr/bin/env bash
# Diagnostic for #193 item 53. None of these roots counts as an accepted
# external project without independently executed original-Lean/Rust parity.
set -euo pipefail

: "${NEWSPEAK_PROJECT:?Pinned unmodified Newspeak Lake project required}"
: "${NEWSPEAK_CASE_DIR:?Existing source-identity evidence directory required}"
: "${NEWSPEAK_NATIVE:?Canonical native backend directory required}"
: "${NEWSPEAK_PLUGIN:?Exact-head native backend shared object required}"
: "${LEAN_PREFIX:?Pinned Lean 4.34.1 required}"

test -f "$NEWSPEAK_PROJECT/Newspeak/PEGCertificate.lean"
test -f "$NEWSPEAK_PROJECT/Newspeak/NewspeakGrammar.lean"
test -f "$NEWSPEAK_PLUGIN"
test "$(cat "$NEWSPEAK_PROJECT/lean-toolchain")" = 'leanprover/lean4:v4.34.1'

out="$NEWSPEAK_CASE_DIR/certificate"
mkdir -p "$out"
manifest="$out/manifest.tsv"
printf 'root\tupstream\tcodegen\trust_build\tsemantic_parity\treason\n' > "$manifest"
{
  echo "status=DIAGNOSTIC_ONLY_NOT_G1_ACCEPTANCE"
  echo "source_repo=newspeaklanguage/newspeak"
  echo "source_commit=$(git -C "$NEWSPEAK_PROJECT" rev-parse HEAD)"
  echo "compiler_commit=$(git -C "$NEWSPEAK_NATIVE" rev-parse HEAD)"
  echo "toolchain=$(lean --version)"
  echo "target=Newspeak.pegGrammarCertificateValid"
  echo "required_followup=source-derived_input_oracles_and_standalone_rust_parity"
  sha256sum "$NEWSPEAK_PROJECT/Newspeak/PEGCertificate.lean" \
    "$NEWSPEAK_PROJECT/Newspeak/NewspeakGrammar.lean" \
    "$NEWSPEAK_PROJECT/Newspeak/FiniteStore.lean" \
    "$NEWSPEAK_PLUGIN"
} > "$out/identity.txt"

# This is a separate, genuinely substantial module. Compile unmodified source
# and genuine dependencies, not a local reimplementation of its algorithm.
upstream='FAIL'
if (cd "$NEWSPEAK_PROJECT" &&
    timeout 150s /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
      -o "$out/upstream.time" lake build Newspeak.PEGCertificate) \
      > "$out/upstream.log" 2>&1; then
  upstream='PASS'
fi
echo "certificate_module_build=$upstream" >> "$out/identity.txt"
if [[ "$upstream" != 'PASS' ]]; then
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    'Newspeak.pegGrammarCertificateValid' 'FAIL' 'NOT_RUN' 'NOT_RUN' \
    'NOT_VERIFIED' 'upstream_module_build_failed_or_timeout' >> "$manifest"
  echo 'upstream certificate module did not compile; no G1 acceptance' > "$out/result.txt"
  exit 0
fi

export LEAN_PATH="$NEWSPEAK_NATIVE:$NEWSPEAK_PROJECT/.lake/build/lib/lean:$LEAN_PREFIX/lib/lean"

# First root is the full acceptance target. Others attribute compiler gaps
# without substituting simpler functions for the certificate checker.
specs=(
  'full|Newspeak.pegGrammarCertificateValid'
  'raw|Newspeak.pegGrammarCertificateValidRaw'
  'references|Newspeak.pegReferencedNames'
)
for spec in "${specs[@]}"; do
  IFS='|' read -r label root <<< "$spec"
  target="$out/$label.rs"
  target_rel="artifacts/external-projects/newspeak/certificate/$label.rs"
  source="$out/$label.lean"
  log="$out/$label.codegen.log"
  printf 'preserve-existing-output\n' > "$target"
  printf 'import NativeRust\nimport Newspeak.PEGCertificate\n#native_rust_closure %s as "external_root" to "%s"\n' \
      "$root" "$target_rel" > "$source"

  codegen='REFUSED'
  rustbuild='NOT_RUN'
  reason='unclassified'
  if (cd "$NEWSPEAK_NATIVE" && timeout 60s /usr/bin/time \
        -f 'wall_seconds=%e peak_rss_kb=%M' -o "$out/$label.codegen.time" \
        lean --load-dynlib="$NEWSPEAK_PLUGIN" "$source") > "$log" 2>&1; then
    if [[ "$(cat "$target")" == 'preserve-existing-output' ]]; then
      echo "FATAL: codegen success without publication for $root" >&2
      exit 1
    fi
    codegen='GENERATED'
    reason='requires_independent_original_Lean_oracles'
    if timeout 30s /usr/bin/time -f 'wall_seconds=%e peak_rss_kb=%M' \
       -o "$out/$label.rust.time" \
       rustc --edition=2024 --crate-type lib -D warnings "$target" \
         -o "$out/$label.rlib" > "$out/$label.rust.log" 2>&1; then
      rustbuild='PASS'
    else
      rustbuild='FAIL'
      reason='generated_rust_did_not_compile'
    fi
  else
    if [[ "$(cat "$target")" != 'preserve-existing-output' ]]; then
      echo "FATAL: unsuccessful codegen mutated preexisting output for $root" >&2
      exit 1
    fi
    rm -f "$target"
    if grep -Fq 'Rust native backend refused' "$log"; then
      reason="$(grep -Fm1 'Rust native backend refused' "$log" | \
        sed 's/.*Rust native backend refused /refused_/' | tr '\t\r\n' '   ' | cut -c1-240)"
    elif grep -Eiq 'timeout|exceeded|killed' "$log"; then
      reason='resource_or_time_limit'
    else
      reason='unclassified_compiler_or_import_error'
    fi
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$root" "$upstream" \
    "$codegen" "$rustbuild" 'NOT_VERIFIED' "$reason" >> "$manifest"
  {
    echo "root=$root"
    echo "generated=$codegen"
    echo "rust_build=$rustbuild"
    echo "semantic_parity=NOT_VERIFIED"
    echo "reason=$reason"
    sha256sum "$source" "$log"
    if [[ -f "$target" ]]; then sha256sum "$target"; fi
  } > "$out/$label.identity.txt"
done

# Deliberately refuse to convert successful codegen into G1 acceptance.
{
  echo 'status=DIAGNOSTIC_ONLY_NOT_G1_ACCEPTANCE'
  echo 'substantial_root=Newspeak.pegGrammarCertificateValid'
  echo 'original_source_module=Newspeak.PEGCertificate'
  echo 'independent_Lean_Rust_parity=NOT_VERIFIED'
  cat "$manifest"
  sha256sum "$manifest" "$out/identity.txt"
} > "$out/result.txt"
