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
exact runtime heap theorem. In particular, Lean's `lean_del_object` frees
only a constructor shell, not its transferred child references. This
admission does not yet establish uniqueness or single-field transfer
requirements for those children, so using an unretained projection after
shell deletion is refused instead of treating it as automatically owned.
The source runtime's actual reference counts may include unmodeled
aliases, so potential final-owner release is conservatively treated as
destruction. General call-result aliasing, externally-owned heap effects,
and source-level lifetime correctness for arbitrary programs remain open. The source verifier conservatively
refuses some correct programs rather than pretending those proofs exist.

The canonical Rust runtime's `Rc` remains a memory-safety mechanism and
the logical source ledger remains separate. The existing same-source Lean C
vs Rust reference-count and two-level destruction experiment is unchanged;
that bounded test also does not prove arbitrary heap simulation.
