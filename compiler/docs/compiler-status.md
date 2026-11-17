# Lean compiler IR to Rust: current status

Snapshot: **November 16, 2026**. This page distinguishes accepted
repository behavior from proposed architecture and open draft work.
Recheck the exact default branch and PR head before treating a later
result as accepted.

| Component | Status | Evidence or next requirement |
| --- | --- | --- |
| Lean source frontend and compiler | Existing Lean 4.34.1 is authoritative | No new Rust parser, elaborator or optimizer |
| In-process compiler IR reader | Implemented for a pinned subset | Borrowed `Lean.IR.Decl` through native ABI; [coverage](../COVERAGE.md) |
| Canonical Rust emitter | Implemented for an explicit subset | [Reader structure](reader-architecture.md); [compiler CLI](../../eth/docs/compiler-ir-backend.md) |
| Rust-emitted object/value runtime | Implemented for bounded subsets | GMP/`Rc` value runtime, [semantic limitations](../SEMANTICS.md) |
| Physical source RC fidelity | Incomplete | Source RC ledger proposed in [PR #283](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/283); no general heap simulation |
| Reader-emitted scalar Rust executed in Lean C host | Implemented for `ScalarFixture.plus` | [Lean C runtime check](../runtime/lean-c/README.md); 100 original-Lean comparisons, scalar only |
| Rust/C ownership boundary witness | Implemented as a bounded integration test | [Lean C runtime bridge](../runtime/lean-c/README.md); not an emitted-Rust runtime |
| Reader-generated heap constructor/projection via Lean C | **Bounded IR subset, undergoing exact-head verification** | [Heap executable comparison](../runtime/lean-c/README.md); nested Pair-in-Box heap child with actual owned transfer and retained projection; general graph/joins unsupported |\n| Generated Rust using Lean C runtime generally | **Not implemented** | Physical ownership parity for remaining IR operations is open |
| Rust-native runtime replacement | **Not established** | Migrate only after C-backed comparison under the [runtime contract](execution-runtime-contract.md) |
| General G1 compiler release | **Open** | [Issue #193](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/193): original project coverage, ownership, ABI, integration |
| Original noncomputable QueryStream (G2) | **Open** | Source-derived residualization, complete execution and resource correspondence |
| Lungo Rust-hosted compiler | Separate optional experiment | [PR #331](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/331) and [bootstrap note](../../docs/lean-rust-replacement.md) |
| Independent Rust proof kernel | Separate project | Does not block any backend or runtime milestone |

## Existing behavior versus intended behavior

The current native compiler consumes Lean compiler IR and, for accepted
cases, embeds a standalone `immutable_value.rs` runtime in the generated
Rust source. Running these binaries without the Lean runtime demonstrates
independence for that **tested subset**. It does not by itself demonstrate
that `Rc` strong counts, borrow transfers, destructor cascades, unique
updates or object identities reproduce the Lean C runtime.

The [paired C/Rust comparison](../COMPARISON.md) measures one set of
executable programs and compiler overhead; it should not be read as a
general runtime-equivalence or performance theorem. Tests with correct
returned values alone do not certify physical ownership behavior.

## Next implementation gate

Generate a Rust program from the actual pinned compiler IR and execute
it against an audited Lean C execution-runtime adapter. Begin with a
constructor, a borrowed projection, explicit reference operations,
`isShared`, a unique/shared update and release, then extend across a
call and a join. Compare original Lean/C and generated Rust/C for:

1. Returned values, errors, side effects and halting.
2. Ownership-sensitive observations: borrowed versus owned references,
   logical count changes, sharing decisions, identity/reuse and
   destruction at specified checkpoints.
3. Reproducible source, IR, runtime ABI, generated Rust and build
   identities, with explicit refusals outside the admitted subset.

Only then substitute Rust-native runtime operations behind the same
emitter/runtime contract. A semantic optimization may change internal
allocation counts, but it must preserve all supported observables under
an independently justified correspondence argument.

See [architecture](backend-first-architecture.md), [runtime contract](execution-runtime-contract.md)
and [G1/G2 acceptance](../../research/lean-rust-acceptance.md).


- Source `del`: physical Lean C shell-only primitive and guarded
  child-credit transfer witness, *not* source-derived IR.del
  execution or general heap semantics.
