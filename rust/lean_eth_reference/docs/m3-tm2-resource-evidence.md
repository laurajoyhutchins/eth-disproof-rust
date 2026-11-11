# Milestone 3, #110: executable primitive tape-resource evidence

**Scope:** a bounded Rust evaluator of the actual finite compiler path
`BitProgram.compileInstr -> FixedParameters.microStep -> StackAdapter.program ->
StackCompiler.controller -> StackMachine.applyAction`. It is **not** a formal
proof translation, imported-Lean differential run, nor an end-to-end native
counter.

Source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.
Compiler definitions and their exact Git blob hashes are now included in
`reference/source-manifest.json`, alongside the preexisting instructions.

## Run it

From `rust/lean_eth_reference`, with the pinned Rust 1.99.1 toolchain:

```sh
cargo test --offline --test tm2_resources
cargo test --offline --release --test tm2_resources
cargo test --offline
cargo fmt --all --check
cargo clippy --offline --all-targets -- -D warnings
cargo run --offline --bin tm2-cost -- 1010
```

The CLI accepts up to 64 literal `0`/`1` bits. It runs the **actual**
`HighIncidenceProgram.Branches.program` built from the Rust source-instruction
table, rather than substituting a semantic SAT oracle. All primitive executions
check each completed instruction boundary against an independently run
`BitProgram.step` and refuse when any boundary disagrees. The caller's
configuration is only committed on success. Source, primitive, tape-visit and
encoded-capacity budgets refuse rather than returning an incomplete result.

## Cost semantics

Counts deliberately measure different objects:

- **Source steps:** complete `BitProgram.step` instructions.
- **TM2 statement microsteps:** executed `TM2.Stmt` constructors, including
  the continuation `goto`; an executed `branch` takes only one arm.
  Lean's `statementSize` bound includes **both** branch arms.
- **Primitive transitions:** individual finite-controller steps from
  `StackCompiler.controller`, including write-self dispatch, fixed-width
  read-return, one action-dispatch or halting step, zero or more physical
  mutation steps, and return-to-ready steps.
- **Head moves/writes:** actual primitive moves and writes counted separately.
  A halting controller transition is neither a move nor a write.
- **Visited cells:** sum of distinct (tape, relative head-position) pairs
  touched, including positions reached by head moves. This is a *visit*
  metric, not allocated memory, a bound on maximum head displacement or
  a bit-complexity theorem.
- **Peak live stack bits:** number of source Boolean values in all stacks.
  **Peak encoded bits:** total nonblank Boolean symbols across all tapes.
  Neither includes finite-control storage, host allocation overhead, nor
  arbitrary-precision integer cost.

For these fixed Boolean stacks, the original encoding gives input tape width
one and all other stacks width two: `StackEncoding.codeOfBoolEquiv` versus
`StackEncoding.codeOfEquiv (Fintype.equivFin Bool)`. The non-input Boolean code
is `[false, bit]`; blank is `none`, not a binary sentinel. Pushing a block
uses reverse-order `move left; write` pairs, popping uses `write none;
move right` pairs, including on empty stacks.

The machine-specific bound follows the actual Lean definitions:

```text
compilerOverhead = max_stack (4 * blockWidth(stack) + 3)
blockOverhead    = max_label statementSize(compileInstr(label))
primitiveOverhead = compilerOverhead * blockOverhead
```

This bound is per complete source instruction, not an assertion that each
instruction actually takes that many primitive transitions. It is finite and
constant for a **fixed program**. It says nothing about how the program size or
its constants vary with the SAT problem parameters.

## Reproduced local results

On the source-defined `HighIncidenceProgram.Branches.program` with mask
`1010`:

| Quantity | Measured |
|---|---:|
| Source instructions | 33 |
| TM2 statement microsteps | 65 |
| Primitive transitions | 390 |
| Tape-head moves | 173 |
| Writes | 216 |
| Distinct visited cells | 28 |
| Peak live stack bits | 10 |
| Peak encoded bits | 19 |
| Per-source-step bound | 33 |

The sum `173 moves + 216 writes + 1 halting transition = 390` checks the
record's primitive transition decomposition.

On a **standalone v0.16 Rust snapshot**, the 9 new `tm2_resources` integration
tests passed in both debug and release; 126 snapshot tests passed overall.
Rustfmt and strict Clippy passed with Rust 1.99.1. The underlying interpreter's
`bit_program.rs` matched the GitHub revision's blob SHA. **The integrated
GitHub branch has not been rebuilt as one checkout**, and the pinned imported
OpenAI Lean/Mathlib environment has not yet executed a differential TM2 trace.

## Explicit remaining acceptance gates

1. Compile and test the **actual combined GitHub PR head** after M1/M2 moves
   stabilize, rather than relying on the standalone Rust snapshot.
2. Execute original imported Lean 4.34.1 with complete SHA-pinned Mathlib,
   compare primitive machine transition sequences and full terminal states.
3. Add a separately written direct transition oracle or imported-source
   primitive trace fixtures. Rust's source `BitProgram.step` comparator alone
   establishes internal consistency, not Lean compiler identity.
4. Measure and/or prove formal tape-space metrics, head displacement,
   finite-control encoding, integer bit-work and physical allocation costs.
5. Connect representative full native counting programs from #107 and source
   preconditions, then examine scaling with encoding, coefficient magnitude,
   widths and recursive expansion.
6. Keep the original Lean `SqrtLogSpace/Final.lean:exact_count_and_sat` theorem
   and any claimed polynomial/subexponential complexity as **unverified
   mathematical obligations**, not implied by these finite tests.

This is an incremental implementation of #110, which remains **open**.
