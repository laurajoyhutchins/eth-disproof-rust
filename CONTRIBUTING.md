# Contributing

This is a source-pinned research port. Each change should make the executed
behavior or the boundaries of the original Lean construction easier to audit.

## Contribution contract

A pull request should answer four concrete questions:

1. **Original source:** Which Lean symbol, file and pinned Git revision is the
   implementation based on? See the [source manifest](rust/lean_eth_reference/reference/source-manifest.json).
2. **Execution:** Is the change an instruction-level source port, a host Rust
   semantic helper, a separate optimization, or a proof-only argument?
3. **Evidence:** Which tests were run on the **exact PR head**, with what
   commands and outputs? For Lean parity, actually execute the pinned
   original Lean implementation and compare all state transitions and halting,
   rather than replaying committed golden fixtures or a second Rust oracle.
4. **Limitations:** What remains unsupported? An absent native stage must
   return an explicit refusal, never a zero count, synthetic halt or silent
   fallback to bounded exponential enumeration.

Keep changes reviewable: one source-defined behavior or one distinct argument
per PR. Do not combine source-faithful translation, performance optimization,
and new mathematical conjectures without separately testing each claim.
Follow the [PR template](.github/PULL_REQUEST_TEMPLATE.md) and
[execution/evidence matrix](rust/lean_eth_reference/docs/evidence.md).

## One Lean-to-Rust compiler path

Maintain the existing source-grounded, compositional exporter and Rust backend;
do not introduce a parallel `lean-rs` generator, runtime, or verification path.
When incorporating ideas from other Lean compilers:

- Let pinned Lean elaboration establish the typed source, rather than parsing
  Lean surface syntax in Rust or guessing source definitions by name.
- Preserve each exported declaration's original Lean name, source revision,
  dependencies, and deterministic generation receipt.
- Report skipped or unsupported definitions with explicit reasons, and refuse
  missing executable dependencies instead of generating placeholder behavior.
- Keep normal Cargo builds and tests independent of a live Lean toolchain;
  source extraction and independent Lean trace checks have explicit gates.
- Attribute copied or adapted implementation code with its upstream path,
  revision and license; see [NOTICE](NOTICE) for design references.

These are compiler acceptance requirements, not claims that all features have
already been implemented or that end-to-end Lean/Rust parity is established.

## Run local checks

From the repository root, `rust-toolchain.toml` pins Rust **1.99.1**
with rustfmt and Clippy:

```sh
cargo fetch --locked
cargo fmt --all -- --check
cargo test --locked --offline --all-targets
python3 -m unittest discover -s rust/lean_eth_reference/tools -p 'test_verify_source_graph.py'
cargo clippy --locked --offline --all-targets -- -D warnings
```

The workspace reuses locked dependencies (including `serde`, `serde_json`
and `sha2`); use `cargo fetch --locked` before offline tests. The
[public Rust workflow](.github/workflows/rust.yml) runs on pull requests,
pushes to `main`, and manual dispatch. Check the actual head SHA and run
conclusion; a previous green run is not evidence for a subsequent commit.

PR checks intentionally run on the submitted **head SHA**, not a synthetic
merge commit. Verify integration on the post-merge `main` SHA separately,
and never claim that a source-graph test fixture proves original Lean parity.

A green Rust workflow validates Rust formatting/tests/lints, **not** the
original Lean semantics, native TM2 refinement or the theorem. Original Lean
execution and mathematical resource accounting require separate evidence.

For a bug report, supply the affected commit, Rust toolchain, smallest
reproducing input (DIMACS when applicable), expected vs actual state/output,
and whether the failure occurs in the Rust port, original imported Lean, or
their comparison.

Original contributions use MIT. Adapted material from
[`openai/math`](https://github.com/openai/math) must preserve applicable
Apache-2.0 license notices and attribution.
