# Runnable Lean ETH native frontend

**Pinned original:** `openai/math@4eaee87548250b2682affda7d05d947c05554bae`, `SqrtLogSpace/NativeFrontend.lean`. The exact original finite physical command is `headerCommand; normalizationCommand; placeBodyCommand; ambientCommand`, compiled as `Native.frontendProgram` (80 registers, 1220 stacks; input port 256, answer port 263).

## Run from a checkout

```sh
cd rust/lean_eth_reference
printf 'p cnf 3 3\n1 0\n1 2 0\n-2 3 0\n' |
  cargo run --offline --locked --bin eth -- frontend
```

The executable parses DIMACS, encodes the original canonical `Encoding.encodeCNF` word, then executes the **physical** Rust BitProgram frontend. Source input stack 256 is preserved, stack 258 contains unary ambient n, stack 267 contains little-endian binary n, and stack 265 contains the normalized CNF body. Stack 263 is **empty**: this frontend does not count SAT assignments. All scratch stacks are empty at completion.

The CLI prints `status=frontend-completed`, actual source instruction count, peak occupied stack bits, and the four output words. The sample above ran locally in **31,578 source instructions** with **420 peak live stack bits**; header words: `ambient_unary=1110`, `variables_binary_lsb=11`.

`--max-steps N` and `--max-stack-bits N` configure refusal limits. Malformed DIMACS and exceeded budgets result in a nonzero exit code and no success output.

## Historical local verification (pre-merge)

Restored Rust **1.99.1**, offline standalone v0.16.0 crate with reconstructed source-native M2 dependencies:
- `cargo test --offline --locked --all-targets`: **148 passed**, debug.
- `cargo test --offline --locked --release --all-targets`: **148 passed**, release.
- `cargo fmt --all -- --check`: **passed**.
- `cargo clippy --offline --locked --all-targets -- -D warnings`: **passed**.
- Source-machine integration tests cover 27 canonical CNFs (empty formulas, empty clauses, unit clauses, tautologies, strict absorption, randomized cases), preserved 80×1220 ABI and finite capacity refusal. Three CLI tests cover DIMACS successful execution, invalid formula refusal and insufficient budget without success output.
- All **four new .rs source/test files** match their locally executed Rust sources byte-for-byte by Git blob hash.

## Verification boundaries

The frontend was merged to `main` in [PR #151](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/151). The local measurements above belong to its original development checkout, not an ongoing benchmark or evidence for later commits. Validate the **exact commit** using the public Rust CI and the [accepted evidence matrix](evidence.md). Original Lean/Mathlib differential parity, primitive TM2 accounting and the end-to-end theorem remain unverified. The real nonterminal high-query path, native leaf, disjoint DFS and noncomputable finite fallback are still unsupported. This frontend does not call the separate enumerating SAT oracle and never fabricates a #SAT answer.
