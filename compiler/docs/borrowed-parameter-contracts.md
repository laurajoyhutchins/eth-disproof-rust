# Direct borrowed-parameter ownership transfer

The pinned Lean 4.34.1 `Lean.IR.Param.borrow` flag is a **source ownership
contract**, not an instruction to clone a Rust `Rc`. Each reachable
function's signature now retains its complete array of borrowed/owned
flags. The direct-call lowering and last-use optimization use these flags:
a Rust handle is never moved through a *borrowed* ABI slot merely because
the variable has no later syntactic use.

The single canonical native compiler runs a source-IR permission
check for **direct borrowed formals and object-pointer projections derived
from them**. A projected field is a borrowed reference until a source
`FnBody.inc` explicitly grants an owned reference. This propagates across
several nested projections and remains visible when the projected value
is passed to a join point. A borrowed
parameter begins with zero transferable references. A nonpersistent
`FnBody.inc` grants an owned credit; direct `dec`, `del`, returning
that parameter, a constructor field or PAP capture, or passing it to an
owned direct callee needs an existing credit. A borrowed-to-borrowed
known direct call consumes no credit. Known read-only primitive arguments
use the exact narrow source adapter list in `reader/borrow.rs`. Unknown
primitive ownership on a directly borrowed argument remains refused.
Case alternatives are checked independently. Join point signatures
also retain their source `Param.borrow` bits. A tracked borrowed or
projected value can enter a borrowed join parameter with no ownership
transfer; entering an owned join parameter requires explicit source
ownership credit. Inside the join body, a borrowed formal starts with
zero owned credits. A join body cannot authorize a transfer in its own
lexical predecessor. Unknown join targets or mutation ownership refuse
when they would transfer tracked borrowed references.

The positive and negative acceptance cases are constructed using **actual
Lean.IR.Param / FnBody / Decl values inside the pinned Lean process** and
passed to the production in-process emitter by
`examples/BorrowFlagFixture.lean`. They test actual packed borrow flags,
owned-to-borrowed forwarding, source `inc` authorizing transfers, and
fail-closed unowned returns, releases, captures, and calls.

## What this does not establish

This is **not** a whole-program ownership proof. It tracks direct
borrowed parameters and the source VarIds of their nested pointer-field
projections, plus explicit owned/borrowed join parameters and jumps.
It does **not** infer aliasing from arbitrary direct-call results, general
constructor storage, mutable object identity, indirect applications or
external primitives. The source-lifetime admission now independently tracks the source owner
credits protecting projected objects, **including projections from owned
formals** (which the borrowed-formal-only audit did not cover). A borrowed
formal remains protected by its caller's owner; owned formals start with one
transferable reference. A projection itself starts with none. Real source
`inc`, `dec`, `del`, direct calls and join transfers update the abstract
state. The reader refuses any projected child read or late `inc` once its
last modeled protecting ancestor is released. Retaining a child before
releasing its parent authorizes later use, including across nested
projections and joins. Join bodies use the state **at each actual jump**,
not at their lexical definition. Mutation conservatively invalidates
projected children when an owning field can be overwritten.

This is a fail-closed *static possible-use-after-release check*, not an
exact runtime heap theorem. The pinned Lean C runtime's `lean_del_object` frees only the constructor
shell, not its child references; `lean_ctor_set` similarly overwrites a
pointer field without decrementing its previous value. The admission
therefore grants the existing slot's source ownership to **one uniquely
identified projection of that exact field** when the shell is deleted
or the field is replaced. Duplicate projections of the same slot are
not independently owned and remain refused without source `inc`.
Fields left unchanged by a different-slot replacement retain their
ordinary parent dependency. For source **owned join parameters**, the
analysis transfers the same object identity and redirects existing
projected child dependencies to the new owning VarId, rather than
pretending the original heap object was destroyed at the jump. When
consecutive `FnBody.set` operations write projections of that same
unique constructor into new slots, the reader admits them only when
their combined origin-slot mapping is bijective on overwritten slots.
This is the exact two-field swap visible in the original pinned
`MutFixture.rotate` IR. A partial permutation, duplicate source
field, or intervening observable operation is rejected. This is a
narrow optimized-IR admission, not certification of arbitrary
reset/reuse or copy-on-write paths.
The lifetime admission accounts for the full source-IR `dec` count rather
than silently consuming one modeled credit. The canonical code generator
and runtime still **refuse nonpersistent `dec` with count != 1**; supporting
larger decrements requires independent pinned Lean C and runtime evidence.
The same source-liveness guard applies to direct object roots, not only
projected children; a direct `proj` after final `dec`, shell `del`, or
owned call is refused. Persistent `dec` remains a source no-op as in the
pinned C emitter.
One narrow source-derived alias is recognized: a direct callee whose
**entire original IR body** returns an owned object formal unchanged. Its
returned reference protects that same allocation after the caller transfers
the argument; the protection ends when the returned owner is released.
Owned and borrowed join formals similarly preserve exact source identity.
No other direct-call result alias, closure, or external return is inferred.
A statically typed Lean IR `tagged` value is an immediate, not a
refcounted source allocation. The lifetime pass therefore does not
allocate or consume ownership credits for tagged declarations or tagged
formals; the normal source IR emitter still checks each operation and
its `checkRef`/persistent flags. Heap-capable `obj`/`tobj` values,
including pointer-field projections, retain source-lifetime checks.
The original optimized `OwnershipFixture.preserveShared` provides an
independent source-native witness: its repeatedly used index `x_9`
is `tagged 0`, not an already-freed heap pointer.
The source runtime's actual reference counts may include unmodeled
aliases, so potential final-owner release is conservatively treated as
destruction. General call-result aliasing, externally-owned heap effects,
and source-level lifetime correctness for arbitrary programs remain open. The source verifier conservatively
refuses some correct programs rather than pretending those proofs exist.

The canonical Rust runtime's `Rc` remains a memory-safety mechanism and
the logical source ledger remains separate. The existing same-source Lean C
vs Rust reference-count and two-level destruction experiment is unchanged;
that bounded test also does not prove arbitrary heap simulation.
