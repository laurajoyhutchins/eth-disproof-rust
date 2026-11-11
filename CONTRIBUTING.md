# Contributing

This is a research port with an intentionally narrow correctness contract. Contributions should make it easier to understand **which original Lean definitions are executed in Rust and which remain unverified**.

## Before opening a pull request

1. Identify the original Lean file, symbol, and source revision affected. The current pinned source identities are in [the manifest](rust/lean_eth_reference/reference/source-manifest.json).
2. Describe the execution boundary: a literal finite instruction port, a Rust semantic helper, an unimplemented stage, or a proof obligation. Do not present a host-language shortcut as a physical-machine translation.
3. Add a focused regression test. If parity with Lean is claimed, provide evidence from **independently executed, pinned Lean**, including the command, toolchain, source revision, and representative outputs. Golden fixtures or Rust-to-Rust comparisons do not establish this parity.
4. Say explicitly what remains unsupported. Where the source program is not implemented, fail closed rather than synthesizing a count, halt, trace, or certificate.

Run from `rust/lean_eth_reference` with Rust **1.99.1**:

```sh
cargo fmt --all -- --check
cargo test --locked --offline --all-targets
cargo clippy --locked --offline --all-targets -- -D warnings
```

The Rust crate has no external Cargo dependencies. The GitHub workflow is dispatch-only; a green Rust check is not evidence of an ETH disproof.

## Review conventions

Keep PRs small and source-linked. Report observed commands and results rather than assumed CI success. Separate mechanical translation, semantics-preserving optimization, and new research claims; each requires different evidence.

For bugs, please include the current commit, Rust version, input (a minimal DIMACS example where applicable), expected and actual output, and whether the failure occurs in the Rust reference or the original imported Lean program.

Original contributions are MIT-licensed. Changes that adapt material from [`openai/math`](https://github.com/openai/math) must retain upstream Apache-2.0 attribution and notice requirements.
