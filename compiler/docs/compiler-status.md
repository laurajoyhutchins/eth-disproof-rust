# Lean compiler IR to Rust: current status

Reviewed against `main` at **November 20, 2026** (`b8c2956`). This is a scoped status snapshot, not an evergreen proof claim. Recheck exact source blobs, CI heads and independent evidence after subsequent changes. The [machine-checkable scoped receipt ledger](../../eth/docs/stage-evidence.md) checks selected unchanged files and historical workflow identities; it does not certify all compiler modules.

| Component | Status | Evidence or next requirement |
| --- | --- | --- |
| Lean source frontend and compiler | Existing Lean 4.34.1 is authoritative | No new Rust parser, elaborator or optimizer |
| In-process compiler IR reader | Implemented for a pinned subset | Borrowed `Lean.IR.Decl` through native ABI; [coverage](../COVERAGE.md) |
| Canonical Rust emitter | Implemented for an explicit subset | [Reader structure](reader-architecture.md); [compiler CLI](../../eth/docs/compiler-ir-backend.md) |
| Rust-emitted object/value runtime | Implemented for bounded subsets | GMP/`Rc` value runtime, [semantic limitations](../SEMANTICS.md) |
| Physical source RC fidelity | Restricted source-credit checks and bounded runtime comparisons | Actual [source lifetime ledger](../backend/src/reader/lifetime.rs) and [source-owned field checks](source-del-final-ir.md) exist; general heap simulation remains open |
| Reader-emitted scalar Rust executed in Lean C host | Implemented for `ScalarFixture.plus` | [Lean C runtime check](../runtime/lean-c/README.md); 100 original-Lean comparisons, scalar only |
| Rust/C ownership boundary witness | Implemented as a bounded integration test | [Lean C runtime bridge](../runtime/lean-c/README.md); not an emitted-Rust runtime |
| Reader-generated heap constructor/projection via Lean C | **Bounded, executed** | [Source-derived IR del](source-del-final-ir.md) with original C/Reader-Rust 720-case comparison; [PR #407](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/407) adds eight source-visible ownership event branches; arbitrary graph/joins remain open |
| Generated Rust using Lean C runtime generally | **Not established** | Restricted generated-Rust/C adapter exists, but no general supported-operation or whole-program refinement theorem |
| Rust-native runtime replacement | **Not established** | Retain the C-backed comparison as an oracle; general alias/destructor behavior under native Rust remains open |
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

Extend the **existing actual generated-Rust-to-Lean-C path**, not another
handwritten test-host simulation. Source-native compiler IR already produces
an executable restricted heap `FnBody.del` with two joins and nested owned
field transfers; the original compiled Lean C function and Reader-generated
Rust/C agree on 720 selected physical-output cases. [PR #407](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/407)
also compared source-visible ownership event sequences for eight branches,
and [PR #419](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/419)
added a source-pinned diagnostic for the actual C++ destructor worklist.

These observations do **not** universally characterize general object
layouts, arbitrary aliases, every compiler control-flow path, all internal
destructor steps, or Rust-native ownership semantics.

The next acceptance gate is a nontrivial extension of admitted `FnBody`
operations and control-flow/alias shapes, compared across original source
and generated Rust/C for **values, ordered effects, identity and sharing**.
A Lean refinement theorem connecting real C++ runtime transitions to the
abstract ownership models is a separate unproved obligation.


See [architecture](backend-first-architecture.md), [runtime contract](execution-runtime-contract.md)
and [G1/G2 acceptance](../../research/lean-rust-acceptance.md).


- Source `del`: physical Lean C shell-only primitive and guarded
  child-credit transfer witness, *not* source-derived IR.del
  execution or general heap semantics.
