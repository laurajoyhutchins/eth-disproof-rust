# G2 original-ETH closure inventory (issue #193, items 42–48)

This tool observes the **actual elaborated Lean definition-body closure**. It
does not compile a Rust executable, certify that an entire declaration is
computational, or claim an ETH result.

The in-process native Lean→Rust backend is the implementation for ordinary
**executable compiler IR**. This inventory exists because the original
`SqrtLogSpace.QueryStreamProgram.program` is source-defined in a noncomputable
section. It may have no compiler IR. Absence of IR cannot license a replacement
algorithm.

## What it does

- Walks definitions using a bounded iterative `Expr` traversal. Revisited
  expressions and declarations are deduplicated; it does not unfold recursors
  or enumerate a `Fin labels → Instr` instruction table.
- Records each original definition-body edge, source symbol, declaration kind
  and whether compiled IR is *observed in the imported environment*. The
  absence of a currently imported IR declaration is only an observation.
- Records axioms, opaque and missing declarations for **review**. A syntactic
  reference does not prove an axiom is computationally relevant; evaluating
  that requires typed erasure/relevance analysis.
- Emits `bounded-incomplete` for a declaration-budget overrun and refuses
  oversized individual expressions. All output explicitly says
  `eth_ready: false`, and no output is a compiler success receipt.

The normal exact-head CI workflow checks the real **Lean 4.34.1** producer on
synthetic multihop axiom, opaque and executable definitions; it checks output
identity, explicit nonacceptance, deterministic repetition and truncation.

## Running the authentic original closure

This is intentionally **not** in the fast PR checkpoint. First use the
existing staged original QueryStream import workflow (currently PR #191) to
build and retain the source-pinned original Lean/Mathlib modules. The source
checkout must be `openai/math@4eaee87548250b2682affda7d05d947c05554bae`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1; the
`instrumentation/lean-env/OAI` symlink must point into that checkout.

Run from this repository root, with the original module already built:

```bash
bash rust/lean_eth_reference/tools/g2-closure/run-original.sh \
  upstream/openai-math \
  instrumentation/lean-env \
  /tmp/eth-g2-original-inventory-1
```

The script verifies the Git commit, clean original worktree, exact
`QueryStreamProgram.lean` blob, Mathlib commit, toolchain and source symlink.
It **imports the real original** `QueryStreamProgram` module, then traverses
the actual closure. No sample declaration or synthetic fallback can satisfy
the run. On a complete syntactic walk it publishes the inventory and a
SHA-256/source-bound observation receipt in a fresh output directory. On
missing original modules, source mismatches, timeout, malformed results or
bounded-incomplete closure, it publishes neither artifact.

`OriginalQuery.lean` is the direct Lean driver. It is not an alternative Rust
backend. The generated inventory is a diagnostic input to the existing
compiler and source-graph paths, not serialized IR required by the in-process
FFI.

## Remaining acceptance obligations

| Issue #193 | Evidence needed before checking the item |
| --- | --- |
| **41, G1 release** | All documented G1-A–E requirements and three independent substantial executable Lean projects must pass; unrelated to this smoke |
| **42, source inventory** | Source-pinned *actual original* import; complete inventory; distinguish actual compiler-IR availability from noncomputable core expressions and computationally necessary axioms |
| **43, lazy residualizer** | Generic, sharing-preserving memoized delta/iota reduction with bounded refusal and source/kernel correspondence; the existing core-Expr DAG only does bounded head beta/zeta |
| **44, physical composition** | Independently validate each actual StructuredCalls/ProgramLinking lowering, including label, PC, register, stack, port and continuation semantics |
| **45, original query compile** | Original `QueryStreamProgram.program`, all its required source-defined composition and a standalone compiled Rust executable; no host SAT oracle |
| **46, trace parity** | Same prepared inputs, independent original Lean/Rust full-state physical traces, explicit counters and first-divergence diagnostics |
| **47, resource/refinement** | Source-to-Rust semantics and primitive TM2 resource/bit accounting established separately, with kernel-checked proof only where actually performed |
| **48, ETH-ready** | All 42–47 completed on the same original pinned source and exact head, with no unsupported/transitively opaque replacement or uncertified shortcut |

The true original module import has previously exceeded runner time limits
before full graph/export/codegen execution. Until the staged import finishes,
there is no original closure certificate and **no change to the status of
items 41–48**. A syntactic inventory is a starting point, not a physical
refinement proof.
