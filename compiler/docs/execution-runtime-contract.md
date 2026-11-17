# Execution runtime contract

**Design contract, not a shipped API.** The canonical compiler IR to Rust
backend currently embeds a standalone value representation from
`runtime/rust/immutable_value.rs`. The next change separates emitted
operations from their execution substrate, without duplicating Lean's
ownership optimizer.

## Boundary

~~~text
Lean compiler IR
    -> one IR reader / emitter
    -> emitted Rust calls to a versioned runtime interface
          -> pinned Lean C runtime adapter       [first]
          -> source-faithful Rust-native runtime  [after comparison]
~~~

The compiler's `frontend/ffi/abi.c` exists to **read borrowed Lean compiler IR
during code generation**. It is not an execution-time Lean C runtime
adapter. The two FFI contracts require separate conformance tests.

The backend must not infer ownership operations from Rust `Clone`,
`Drop` or `Rc::strong_count`. The final Lean compiler IR already
specifies reference operations. Rust's type system may help enforce
the boundary, but cannot silently change source decisions.

## Operation obligations

These are required *semantic* operations, not finalized Rust API names.

| IR/runtime event | Required contract |
| --- | --- |
| Incoming owned or borrowed parameter | Distinguish ownership; a borrow does not independently acquire the object |
| Move/transfer | Transfer the existing reference without an invented increment |
| `inc`, `dec`, `del` | Implement source-defined reference transitions, including flags, immediates and shell-only deletion where applicable |
| Constructor allocation and fields | Preserve object kinds, pointer/scalar layouts, identities and field ownership |
| `proj`, `sproj`, `uproj` | Respect borrowed/owned and scalar-byte projection rules; do not conflate them |
| `isShared` and reusable allocation | Preserve the source's sharing observation and unique/shared mutation behavior |
| Arrays, strings, closures and PAP/AP | Preserve captured/element ownership, application and release effects |
| Direct/indirect calls, joins and FFI | Preserve evaluation order, argument modes, borrowed lifetimes, exceptional exits and destructor cascades |

A primitive or external function must have a verified implementation
and precise failure behavior. Persistent/sticky/frozen state,
multithreading, effects and unknown externs remain distinct obligations.
If a contract cannot be implemented safely for an encountered shape,
refuse the whole compilation without publishing output.

## Initial physical Lean C bridge

The [execution-time FFI bridge](../runtime/lean-c/README.md) uses
actual Lean C `lean_object *` ownership, `lean_inc`/`lean_dec`,
constructor fields and physical source count observation. Its
independent compiled-source witness compares the original Lean C
`OwnershipObjectTrace.create` with the bounded Rust/C handle API.
The runtime gate now additionally links the **exact Reader-generated**
`ScalarFixture.plus` Rust function into a Lean C-hosted executable and
compares 100 scalar input pairs against the original Lean source. This
validates the initial emitted-function C ABI, but only for an unboxed
scalar function. The generated heap-backed Rust still does not select
the Lean C runtime.

## Lean C-backed baseline

1. Pin the exact Lean compiler/runtime version and C headers; test
   ABI agreement and FFI unwind/error boundaries.
2. Produce generated Rust from a *real* `Lean.IR.Decl` closure. Use a
   single selectable runtime implementation, not two emitters.
3. Call the existing Lean C implementation for accepted runtime
   operations. Specify owned, borrowed and transferred arguments and
   results for every entry point.
4. Execute the **original Lean source via Lean C** independently.
   Record observable values and, on an explicit witness corpus,
   allocation identity, refcount transitions, sharing, reuse and
   destruction at well-defined checkpoints.
5. Refuse semantic shapes outside the tested contract, including
   cross-thread states and unfamiliar runtime externs.

An execution trace is evidence only for the tested cases. Physical
trace matching over a finite corpus does not prove all programs
correspond. Record the remaining proof obligations separately.

## Rust runtime substitution

Only after the C-backed baseline passes for a feature family should
a native Rust runtime operation become selectable. Re-run the same
source-origin tests without changing the emitter. Compare externally
visible values, errors, effects and observable sharing and mutation.
Where the Rust implementation intentionally removes redundant
allocations or refcount operations, prove or check that the
corresponding observations cannot distinguish the optimization.

The initial conservative requirement is *physical agreement* for the
C-backed baseline; the later optimized Rust implementation requires
*contextual semantic agreement* and measured time, allocations and
peak space. These claims must not be merged into one test result.

## Concrete first witness

Compile an unchanged Lean source program to final compiler IR,
generate Rust that uses the C adapter, then execute unique and
shared constructor cases with a borrowed field projection,
`inc/dec`, `isShared`, a release, and one call/join edge.
Compare independent Lean/C and Rust/C behavior and ownership traces.
Keep source-program IDs, compiler revisions, runtime versions,
generated source digests and exact CI head in the receipt.

This work is G1. It neither proves a new independent proof kernel nor
makes the original noncomputable ETH QueryStream program executable.

See the [architecture](backend-first-architecture.md),
[status](compiler-status.md), [current semantics](../SEMANTICS.md)
and [compiler acceptance issue](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/193).
