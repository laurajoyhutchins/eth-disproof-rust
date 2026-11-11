# Rust port of the OpenAI ETH Lean program

This branch contains the Rust implementation and its source-conformance
infrastructure. The pre-existing Python/Cython Sudoku solver, counting
experiments, benchmarks, proofs-in-progress, and their history live on
[the `python/sudoku-research` branch](../../tree/python/sudoku-research).

## Implementation

The Rust crate is at [`rust/lean_eth_reference/`](rust/lean_eth_reference/).
It ports executable finite semantics and selected source-defined BitProgram
components from [`openai/math` at `4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT).

```sh
cd rust/lean_eth_reference
cargo fmt --all -- --check
cargo test --locked --offline --all-targets
cargo clippy --locked --offline --all-targets -- -D warnings
```

Use `cloudbuild.rust.yaml` for isolated Rust verification. The
`.github/workflows/rust.yml` workflow also targets this crate, without
running the Python/Cython solver suite.

**Scope:** This is an incomplete Lean-to-Rust port, not a proven ETH disproof,
a complete native counting program, or a verified complexity theorem.
Some finite machines execute; remaining stages explicitly refuse or are
unimplemented. Genuine pinned-Lean/Rust differential verification is
still required. See the crate's implementation notes and test cases.

The `.lean` fixtures and small Python comparison scripts *inside the Rust
crate* are conformance tooling, not the former Python Sudoku implementation.

## A guided reading of the Git history

The `main` first-parent commits teach the port in dependency order, from
finite CNF semantics and the bit-machine through source-defined query,
cache, signature and pair stages. They are exact historical source trees,
not a claim that the full Lean theorem is executable.

Run `git log --first-parent --reverse --oneline main` and follow
[the reading guide](rust/lean_eth_reference/docs/reading-the-history.md).
The original development ancestry remains reachable without a force-push.

## Branches

- `main`: Rust implementation and Rust-specific verification.
- `python/sudoku-research`: intact pre-split Python/Cython research tree,
  tests, benchmarks, configuration, and historical commits.

Open Python/Cython pull requests should target the research branch; Rust port
pull requests should target `main`.
