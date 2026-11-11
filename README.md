# OpenAI ETH construction: Rust execution study

This repository is an independent, source-pinned Rust implementation study of
selected executable programs in OpenAI's Lean development,
[*The Exponential Time Hypothesis is False*](https://github.com/openai/math/blob/main/lean/docs/378.md).
It is **not** an independent proof of ETH's negation. In particular, the full
native counting path, an independently executed Lean/Rust differential, and the
claimed asymptotic resource bounds are not established on `main`.

## Run the source-defined frontend

From the repository root, the checked-in `rust-toolchain.toml` pins **Rust 1.99.1**:

```sh
cargo test --locked --offline --all-targets
printf 'p cnf 3 3\n1 0\n1 2 0\n-2 3 0\n' | \
  cargo run --quiet --locked --offline -p lean-eth-reference --bin eth-frontend
```

This runs the pinned `Native.frontendCommand` as a Rust finite
register-and-stack machine. It parses and normalizes a CNF and reports the
resulting physical stack words, instruction total and peak occupied stack bits.
**It does not count satisfying assignments.** See the
[frontend specification](rust/lean_eth_reference/docs/m2-runnable-frontend.md).

For a separate, explicitly **exponential** bounded #SAT correctness oracle:

```sh
printf 'p cnf 3 2\n1 2 0\n1 3 0\n' | \
  cargo run --quiet --locked --offline -p lean-eth-reference --bin lean-eth-reference
```

That example has 5 solutions. The oracle does not execute the proposed ETH
algorithm and refuses unsupported instance sizes.

## Current scope

| Accepted on `main` | Still open |
| --- | --- |
| CNF parsing, encoding and bounded semantic oracle | Complete source-defined nonterminal #SAT count |
| Rust bit-machine interpreter and runnable native frontend | Independently executed original Lean/Rust full-state differential |
| Source-correlated instruction fragments, generated literal tables and supported terminal-family native counts | Primitive TM2 refinement and worst-case complexity argument |

The root `Cargo.toml` is the canonical workspace manifest and the root `Cargo.lock` is the sole dependency lockfile. The Rust crate remains at `rust/lean_eth_reference`; from that directory, ordinary Cargo commands also resolve the workspace.

The authoritative [execution and evidence matrix](rust/lean_eth_reference/docs/evidence.md)
explains what each test actually establishes and how to reproduce it. The
[port dependency inventory](rust/lean_eth_reference/docs/remaining-lean-port.md)
identifies missing stages; a constructor that is still unavailable must refuse
rather than supply a synthetic answer.

## Source, checks and history

- [Rust crate and CLI guide](rust/lean_eth_reference/README.md)
- [Pinned Lean source manifest](rust/lean_eth_reference/reference/source-manifest.json):
  [`openai/math@4eaee875`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT)
- [Rust CI](.github/workflows/rust.yml): Rust formatting, tests and strict Clippy
  on PRs, `main` pushes and manual dispatch
- [Study guide to the Git history](rust/lean_eth_reference/docs/reading-the-history.md):
  the first-parent teaching sequence is explicitly reconstructed, not
  original chronological authorship

Earlier Python/Cython Sudoku research is retained on the
[`python/sudoku-research` branch](https://github.com/laurajoyhutchins/eth-disproof-rust/tree/python/sudoku-research);
it is not part of the default Rust executable.

## Contributing, provenance and licensing

Please keep behavioral evidence distinct from source identity, native
performance measurements and mathematical complexity proofs. See
[CONTRIBUTING.md](CONTRIBUTING.md) for source-linked changes and reproducible
test requirements.

This is independent research, not an official OpenAI release. Original
contributions use the [MIT license](LICENSE); adapted upstream material has
[Apache-2.0](LICENSE-APACHE) obligations described in [NOTICE](NOTICE). The
Rust crate records `MIT AND Apache-2.0`.
