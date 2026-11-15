# Direct borrowed-parameter ownership transfer

The pinned Lean 4.34.1 `Lean.IR.Param.borrow` flag is a **source ownership
contract**, not an instruction to clone a Rust `Rc`. Each reachable
function's signature now retains its complete array of borrowed/owned
flags. The direct-call lowering and last-use optimization use these flags:
a Rust handle is never moved through a *borrowed* ABI slot merely because
the variable has no later syntactic use.

The single canonical native compiler also runs a source-IR permission
check for **direct references to borrowed formal parameters**. A borrowed
parameter begins with zero transferable references. A nonpersistent
`FnBody.inc` grants an owned credit; direct `dec`, `del`, returning
that parameter, a constructor field or PAP capture, or passing it to an
owned direct callee needs an existing credit. A borrowed-to-borrowed
known direct call consumes no credit. Known read-only primitive arguments
use the exact narrow source adapter list in `reader/borrow.rs`. Unknown
primitive ownership on a directly borrowed argument remains refused.
Case alternatives are checked independently, including their own credit
balances; an unverified borrowed jump transfer or mutation refuses.

The positive and negative acceptance cases are constructed using **actual
Lean.IR.Param / FnBody / Decl values inside the pinned Lean process** and
passed to the production in-process emitter by
`examples/BorrowFlagFixture.lean`. They test actual packed borrow flags,
owned-to-borrowed forwarding, source `inc` authorizing transfers, and
fail-closed unowned returns, releases, captures, and calls.

## What this does not establish

This is **not** a whole-program ownership proof. It only tracks the named
formal parameter directly. References to a borrowed object's child,
aliases returned by other functions, stored references, indirect closure
calls, cross-join ownership propagation, and general heap mutation need a
separate provenance and lifetime analysis. The source verifier conservatively
refuses some correct programs rather than pretending those proofs exist.

The canonical Rust runtime's `Rc` remains a memory-safety mechanism and
the logical source ledger remains separate. The existing same-source Lean C
vs Rust reference-count and two-level destruction experiment is unchanged;
that bounded test also does not prove arbitrary heap simulation.
