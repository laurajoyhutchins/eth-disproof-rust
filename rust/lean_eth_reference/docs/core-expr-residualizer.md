# Generic Lean core-expression residualizer (stacked on PR #184)

Status: **working isolated Lean producer; symbolic only; no executable ETH port**.

## Two-path compilation contract

The compiler-IR backend handles declarations for which Lean actually supplies compatible executable IR. Missing IR is not evidence that a different host algorithm may be used. A source declaration without suitable IR enters the symbolic path, or fails closed. Both paths must ultimately establish correspondence to the **same original elaborated Lean declaration** and source revision.

| Result | What it establishes | What it does not establish |
| --- | --- | --- |
| `generated-unverified` (IR probe) | The external backend returned and wrote source for the requested executable roots | Lean/Rust semantic equivalence or physical BitProgram parity |
| `residualized-unverified` (this producer) | Lean extracted the definition body, produced a shared core `Expr` DAG, and checked its conservative head β/ζ reductions for definitional equality | Executability, transitive closure completeness, Rust semantic equivalence, or BitProgram parity |
| Refusal | The requested path did not produce an accepted artifact | Permission to substitute an implementation |

**No output of the residualizer may be executed or certified as a counting algorithm yet.** Its output explicitly sets `rust_executable=false` and `physical_refinement=not-established`.

## Why this is generic

The producer walks the **finite, stable grammar of Lean's elaborated core `Expr`**, not the open-ended collection of `StructuredCalls`, linking operations, algebraic lemmas, or user-level constructs. All binders use de Bruijn indices; constants carry structured `Name` values and universe arguments. Sharing is retained using a hash map keyed by structural `Expr` identity. Nodes are emitted in dependency-before-parent order. Nested metadata wrappers are dropped because they do not change reduction semantics.

The source body is obtained from `getConstInfo`, including a `noncomputable def`; it is not simulated with a Rust approximation. At the head, at most 16 syntactic β/ζ reductions are applied and checked with Lean `Meta.isDefEq`. A `Nat.rec` with an enormous literal argument remains symbolic: no recursor unfolding, instruction table enumeration, or recursive `whnf` of the whole program is attempted.

This producer refuses free/metavariables, unresolved universe metavariables, non-definition roots, direct dependencies on axioms or opaque constants, and expression/depth budget overruns. **The blocker scan is currently direct, not transitive**. Until executable closure analysis is added, it cannot classify any emitted graph as executable, even when the blocker scan is empty.

## Run the real Lean tests

The original Lean producer remains `tools/lean-ir-smoke/ResidualGraph.lean`.
The smoke harness has been ported to a **Rust integration test**, including
symbolic sharing, bounded beta/zeta reduction, large `Nat.rec` preservation,
universe polymorphism and three refusal cases. Supply an actual Lean binary:

```sh
LEAN_BIN=/path/to/lean cargo test --locked --test lean_residual_real
```

Without `LEAN_BIN` the optional real-Lean test does not execute; a normal
Cargo CI pass must not be described as real Lean differential evidence.
The previous isolated Lean 4.34.1 and 4.35.0 runs were performed before this
migration. The source semantics and Rust contract still require independent
physical-machine verification.

For checked-out projects, the `eth-compiler compile --backend residual-expr`
command invokes Lean and then validates the emitted graph against the same
Rust contract used by the compiler-IR path. See
[two-path acceptance contract](two-path-acceptance-contract.md).

For a simple interactive probe, first compile `ResidualGraph.lean` to `ResidualGraph.olean` in the Lean module path. In another module, import `ResidualGraph` and the source module, then use:

```lean
#export_residual_graph MyNamespace.myDefinition
```

The successful command prints exactly one JSON graph line. Errors print no graph artifact. A caller must additionally bind the declaration to its original source Git blob, Lean/Mathlib pins, and exact generated graph SHA-256 before consuming it. The current isolated command deliberately does not manufacture a provenance receipt for an unverified repository.

## Required next implementation gates

1. Build a typed Lean-side decoder/round-trip checker with a kernel-checked witness for every accepted reduction; do not treat `isDefEq` reporting alone as an external proof certificate.
2. Traverse the actual transitive computational declaration closure; distinguish proof-only axioms from computationally relevant axiom dependencies, refusing the latter.
3. Add demand-driven delta/iota reduction and memoized substitution under explicit resource limits, without forcing `Fin l → Instr` tables.
4. Bind the DAG to the original Lean 4.34.1/Mathlib source pin and its exact Git blobs, emitting a shared versioned receipt with the IR path.
5. Define a typed, non-eval Rust consumer for the DAG and prove/dependently check preservation when lowering its individual operations.
6. Independently compare original physical label, PC, ports, transition, and cost traces before marking `SqrtLogSpace.QueryStreamProgram.program` executable.

The original ETH-specific source exporter remains in place. This experiment is an additional mechanism, not an assertion that the full ETH program has been compiled.
