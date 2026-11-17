# OpenAI ETH construction: Rust implementation study

This repository studies the counting machine defined in [OpenAI's Lean ETH construction](https://github.com/openai/math/blob/main/lean/docs/378.md). The implementation preserves source identities, compiles supported operations to Rust, and uses independent Lean execution to check correspondence where available. Performance work is evaluated against the total counting cost.

**Current boundary:** the source-defined frontend and selected machine fragments run. A complete general nonterminal #SAT count and its primitive-machine complexity bound are not yet established on `main`.

## Build and run

The Rust toolchain is pinned to **1.99.1**. From the repository root:

```sh
cargo test --locked --offline --all-targets

# Execute the source-defined frontend (not a #SAT counter).
printf 'p cnf 3 3\n1 0\n1 2 0\n-2 3 0\n' | \
  cargo run --quiet --locked --offline -p lean-eth-reference --bin eth-frontend
```

That frontend runs `Native.frontendCommand` as a physical register-and-stack machine and reports instruction and occupied-stack-bit counts. It does not report the number of satisfying assignments.

To check a small answer with the **separate exponential oracle**:

```sh
printf 'p cnf 3 2\n1 2 0\n1 3 0\n' | \
  cargo run --quiet --locked --offline -p lean-eth-reference --bin lean-eth-reference
```

The formula has **5** satisfying assignments. The oracle uses bounded enumeration and is separate from the proposed algorithm.

For executable boundaries, see [the evidence](rust/lean_eth_reference/docs/evidence.md), [missing source stages](rust/lean_eth_reference/docs/remaining-lean-port.md) and the [frontend interface](rust/lean_eth_reference/docs/m2-runnable-frontend.md).

## Lean compiler IR to Rust

This is a separate G1 compiler project within the repository, not a replacement Lean parser or proof kernel. Lean 4.34.1 remains responsible for parsing, elaboration, ownership lowering and executable compiler IR. The [canonical native backend](rust/native_lean_backend/README.md) reads that IR in process and emits Rust for a bounded supported subset. The current generated code embeds a Rust value runtime; it has not established complete physical reference-count equivalence with Lean.

The next step is to execute generated Rust against **Lean's existing C runtime through an audited adapter**, compare output and ownership traces, and only then replace individual runtime operations with native Rust equivalents. No C-backed generated execution adapter is claimed complete today. An independent Rust proof kernel belongs to a separate project. The Lungo experiment is not the production code generator.

Read the [architecture](rust/native_lean_backend/docs/backend-first-architecture.md), [current status](rust/native_lean_backend/docs/compiler-status.md), [runtime contract](rust/native_lean_backend/docs/execution-runtime-contract.md) and [compiler CLI](rust/lean_eth_reference/docs/compiler-ir-backend.md). The ETH-specific noncomputable QueryStream source still has its own G2 executable-correspondence obligation.

## Mathematical research

- [The 2-adic recursion](research/two-adic-recursion.md): packets, weighted modes, group contraction and the Lean theorem still needed.
- [Spectral group actions](research/spectral-group-actions.md): pair swaps, Krawtchouk structure and what compression must preserve.
- [The cost of the complete algorithm](rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md): the enormous parameter regime, precision, packet work, interpolation and leaf sizes.
- [Lean-to-Rust correspondence](research/lean-rust-acceptance.md): why a compiler-IR backend alone cannot execute a noncomputable source declaration.
- [Research record](research/README.md) and [literature](research/literature.md).

## Documentation

The [MkDocs site](docs/index.md) renders the existing Markdown with navigation, search, and equations.

```sh
python3 -m pip install -r docs/requirements.txt
python3 -m mkdocs serve
# Check the generated site:
python3 -m mkdocs build --strict
```

The documentation workflow builds a static-site artifact. A public GitHub Pages URL is not implied by that build.

## Source and provenance

The [manifest](rust/lean_eth_reference/reference/source-manifest.json) pins `openai/math@4eaee87548250b2682affda7d05d947c05554bae`. The canonical Cargo workspace lives at the repository root; the implementation crate is `rust/lean_eth_reference`. [Source and tests](rust/lean_eth_reference/README.md), [contributing rules](CONTRIBUTING.md), and [the historical port record](rust/lean_eth_reference/docs/reading-the-history.md) document the implementation history.

Earlier Python/Cython Sudoku experiments remain on the [historical research branch](https://github.com/laurajoyhutchins/eth-disproof-rust/tree/python/sudoku-research). They are not the active Rust counter.

This is independent research, not an official OpenAI release. Original work is [MIT](LICENSE); upstream adaptations and notices are documented in [Apache-2.0](LICENSE-APACHE) and [NOTICE](NOTICE).
