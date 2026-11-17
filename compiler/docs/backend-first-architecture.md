# Backend first: Lean compiler IR to Rust

**Decision (2026-11-16).** Keep Lean 4's parser, elaborator, compiler,
and proof checker authoritative. Build one Rust code generator from Lean's
ownership-explicit compiler IR. Validate generated Rust with the existing
Lean C runtime before attempting to replace that runtime. An independent
Rust proof kernel is a separate project, not a dependency of this compiler.

**Status:** architectural acceptance contract, **not** a claim that the
existing backend or runtime already satisfies it.

## Boundary

```text
Lean 4 source (programs, definitions, proofs)
    -> existing Lean frontend, elaborator and compiler
    -> Lean.IR.Decl / closed executable compiler-IR graph
    -> one Rust emitter
    -> generated Rust + one versioned runtime interface
         |-- pinned Lean C runtime adapter (first)
         `-- native Rust runtime adapter (later)
    -> independently compared execution
```

LCNF is useful to inspect optimizations and ownership lowering, but is
not a second production emitter. Do not reimplement parsing,
elaboration, Lean's ownership-placement passes or compiler
optimizations in Rust. Compile from the final executable IR and preserve
its explicit instructions, evaluation order and argument ownership.

The **runtime interface** is the seam between backend and substrate.
Select one implementation per generated target without changing the IR
lowering. The first implementation forwards operations to Lean's
version-pinned C runtime via audited FFI. The later Rust implementation
must meet the same contract before it replaces any part of that adapter.
An opaque Lean object pointer is an interop representation, not an
excuse to assume Rust `Rc` aliases equal Lean-owned references.

## Existing repository and disposition

| Existing work | Role under this decision |
| --- | --- |
| `compiler/src/reader/` and `src/lib.rs` | **Canonical backend** and current regression baseline. Retain one IR reader and one emitter. |
| `compiler/src/runtime/immutable_value.rs` | Current standalone Rust value runtime for an admitted subset; preserve its tests, but do **not** treat output equality or `Rc::strong_count` as proof of Lean ownership fidelity. |
| `compiler/native/abi.c` | Version-pinned, borrowed IR access during compilation; distinguish this from the *new* execution-time Lean C runtime adapter. |
| PR #283 | Integrate source RC ledger and emitter work only after reconciling with main; single-threaded scope does not imply full physical RC fidelity. |
| PR #331, `experiments/lean-compiler-bootstrap` | Optional, isolated experiment in compiling original Lean compiler modules. Not a replacement frontend, not a required bootstrap, not a second production backend. |
| Original ETH QueryStream source graph | A distinct **G2 residualization** obligation; never represent its source graph as an ordinary executable `Lean.IR.Decl` when no such IR exists. |

No existing implementation is retired solely because this document exists.

## Backend obligations (P0)

The canonical backend consumes a *closed* executable declaration graph,
with original Lean declaration identities and deterministic imports. It
must either emit an executable Rust target or refuse **the whole target**
with the first unsupported source declaration and IR construct.

In its published supported domain, cover:

1. Returns, `cases`, join points, direct/indirect calls, recursion and
   closures, with source evaluation order and argument modes.
2. Constructors, projections, tagged values, allocation, reset/reuse,
   primitives, and persistent/shared cases.
3. Every encountered explicit `inc`, `dec`, `del`, borrow and ownership
   transfer. Do not erase RC instructions because Rust values happen to
   clone or drop.
4. Versioned IR and primitive inventories, with negative tests for
   unsupported constructs, externs and effects. No guessed fallback.
5. Transactional output publication, pinned Lean/Rust versions, and a
   reproducible independent Lean oracle for each admitted feature family.

A supported subset is acceptable. Calling it *general Lean* before the
G1 feature floor and independent project gates pass is not.

## C-runtime-backed execution (P1)

Introduce a single module of runtime operations used by **generated**
Rust code. Start with a Lean C adapter using the pinned Lean runtime.
Do not confuse the existing compile-time `lean.h` reader with this
execution-time adapter.

For each operation, specify its input and result ownership (owned,
borrowed or transferred), null/tagged handling, allocation identity,
error behavior, and effect on the reference-count state. At minimum the
interface must cover retained/released object references, constructors,
projection, arrays, closures, application and the primitives admitted by
the backend. Add operations only when their exact Lean C behavior is
understood.

An explicit move is not an increment; a borrowed projection is not an
owned return; deletion of a shell is not recursive final release. Keep
these distinctions visible at the emitter/runtime boundary. Prevent
implicit Rust `Clone`/`Drop` from silently inventing Lean refcount
events.

## Verification (P2)

Run the *same source declaration and input* through three separately
identified paths, progressively:

1. Lean's compiler and native C execution (reference).
2. Rust emitted from the exact Lean compiler IR, using Lean's C runtime
   through FFI (backend correspondence).
3. **Later:** the same emitted Rust against the Rust-native runtime
   (runtime correspondence).

Record exact source, IR, runtime version, generated artifact and tool
hashes. Compare outputs, effects, errors and observable mutation.

For ownership-sensitive witnesses, additionally record object identity,
source `inc/dec/del`, borrow/transfer, `isShared`, reuse/reset,
allocation and destruction at well-defined semantic checkpoints. Test
aliasing through branch joins, field projections, arrays, closures,
foreign calls and destructor cascades. Model sticky/frozen,
persistent and multithreaded states separately; never extrapolate a
single-threaded trace to them.

**Two distinct claims:**

- **Baseline physical fidelity:** the C-runtime adapter matches Lean's
  relevant physical operations and lifetimes on the admitted domain.
- **Optimized semantic fidelity:** the native Rust runtime may omit or
  combine operations *only after* proving or testing the relevant
  contextual observations unchanged. Identical physical operation counts
  are not required for a validated optimization, but observed ownership
  behavior and externally visible effects must remain correct. If the
  observation model is insufficient, refuse rather than optimize.

Tests give finite evidence. A general semantic-preservation claim needs
an independently checked simulation/refinement argument; an output
checksum alone does not establish it.

## Native runtime (P3), performance (P4)

After P0-P2 succeed for a feature family, implement that family in the
Rust-native runtime behind the **same** interface. Migrate by operation
and fixture, not by rewriting the backend. Use Rust's type/ownership
system to encode obligations where possible, but do not substitute
`Rc` semantics for Lean's source semantics without an equivalence
argument.

Benchmark matched programs against Lean C and both generated-Rust
runtimes: frontend/lowering time, emitted size, Rust build time, run
time, allocations and peak RSS. Any speedup claim must include
equivalent work and the cost of runtime indirection/FFI. Track
performance only after the corresponding semantic gate passes.

## Separate projects and gates

The **proof kernel** can independently recheck proof terms in a
different repository. No proof kernel work blocks the Rust backend, and
a Rust executable is not by itself a proof checker.

**G1:** compile and execute original, closed, computable Lean programs
with explicit coverage and independent correspondence.

**G2:** reduce original noncomputable ETH program constructions to
justified executable representations, or refuse them. G1 does not solve
G2, and neither establishes the manuscript's time/space theorem.

## First mergeable implementation slice

Build **one end-to-end Lean C runtime target** through the canonical
emitter: a source program that allocates a constructor, projects a
borrowed field, increments a source reference, observes sharing,
releases references and returns a value. Include a shared and a unique
execution, then test a join/call crossing. Require original Lean/C
output and physical trace equality on this restricted case. Refuse
other ownership-sensitive patterns until covered.

This first target is deliberately *not* a new object engine, a second
backend or an unrestricted portability layer. It provides the
independent baseline against which the existing `immutable_value.rs`
runtime and PR #283 can be judged.
