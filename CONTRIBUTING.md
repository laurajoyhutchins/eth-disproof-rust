# Contributing

This is a source-pinned research port. Each change should make the executed
behavior or the boundaries of the original Lean construction easier to audit.

## Contribution contract

A pull request should answer four concrete questions:

1. **Original source:** Which Lean symbol, file and pinned Git revision is the
   implementation based on? See the [source manifest](rust/lean_eth_reference/reference/source-manifest.json).
2. **Execution:** Is the change an instruction-level source port, a host Rust
   semantic helper, a separate optimization, or a proof-only argument?
3. **Evidence:** Which tests were run, against which **exact tested commit**,
   with what commands and outputs? For Lean parity, actually execute the pinned
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

## Fast Rust checkpoint

From the repository root, the checked-in `rust-toolchain.toml` selects
Rust **1.99.1**, including rustfmt and Clippy:

```sh
cargo fetch --locked
cargo fmt --all -- --check
cargo test --locked --offline --workspace --all-targets
cargo clippy --locked --offline --workspace --all-targets -- -D warnings
```

`cargo fetch --locked` obtains any missing locked dependencies once; subsequent
offline checks do not download crates. Keep these checks together. Do not
introduce parallel compilation jobs or a remote build service for this small
workspace without measured evidence that it helps.

The [Rust workflow](.github/workflows/rust.yml) runs on pull requests,
pushes to `main`, and manual dispatch. On PRs GitHub checks out the
proposed merge commit; record both the tested merge SHA and the PR head SHA
when reporting evidence. For **exact PR-head** evidence, run the commands
directly against that head, not against the synthetic merge commit. A green
run on an earlier commit is never evidence for a later commit.

## Independent source verification

The [pinned Lean literal extractor](.github/workflows/lean-extraction.yml)
runs only when extraction code or fixtures change, or when manually dispatched.
It fetches the original source at a pinned revision and verifies generated
literal tables. It does **not** run the full original Lean semantics.

A green Rust workflow validates Rust formatting, tests and linting, **not**
original Lean semantics, native TM2 refinement or the theorem. Expensive
original-Lean execution and independent Lean/Rust differential checks must
remain separate, with successful evidence recorded on the relevant source
revision before claiming parity.

For a bug report, supply the affected commit, Rust toolchain, smallest
reproducing input (DIMACS when applicable), expected vs actual state/output,
and whether the failure occurs in the Rust port, original imported Lean, or
their comparison.

Original contributions use MIT. Adapted material from
[`openai/math`](https://github.com/openai/math) must preserve applicable
Apache-2.0 license notices and attribution.
