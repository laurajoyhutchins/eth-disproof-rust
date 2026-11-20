# Bounded effect-order correspondence at the canonical Reader

**Status:** a source-derived *syntactic order* guard and an independently
kernel-checked **abstract** effect model. This is not a new ownership
optimizer, a complete compiler simulation, or a Lean C runtime theorem.

## What is checked

The canonical `Reader::emit_function` already decodes the real, borrowed,
pinned `Lean.IR.Decl` and emits Rust. Before publishing one generated function,
`linear_source_effects` independently walks the **same original compiler IR**
for a strictly straight-line fragment:

- `FnBody.vdecl` of a literal or `Expr.isShared`;
- `FnBody.inc`, `FnBody.dec`, `FnBody.del` with their actual variable
  indices, counts, `checkRef`, and `persistent` bits;
- an ordinary `FnBody.ret`.

For this fragment only, the checker scans the already emitted function's
canonical Rust statements and demands exact equality of the sequence:
`is_shared`, `source_inc`, `source_dec`, and `source_del` events, including
operands, destinations, counts and flags. A change, omission, insertion,
reordering, or malformed recognized operation refuses output.

`jdecl` / `jmp`, `case`, calls, mutation, constructor/projection expressions,
unknown tags, and any other non-literal expression receive **no receipt**
from this pass. Their preexisting Reader admission and refusal rules are
unchanged. A receipt is not silently created by assuming that two Lean
variable IDs represent distinct allocations.

The source events are independently decoded from borrowed compiler IR
by `reader/effect_source.rs`. The emitted events are parsed from the actual
Rust string by `reader/effect_order.rs`. No second emitter is introduced.
The check occurs before the function text is returned for transactional
publication. The parser recognizes a deliberately tiny generated-language
grammar and is **not** a complete Rust AST parser.

## Mathematical boundary

`proofs/ReaderEffectOrder.lean` models a total, single-threaded object
reference-count map with `retain` and `observe`. Pinned Lean 4.34.1
kernel checks establish:

- retain updates the named allocation's count only;
- other allocations' sharing observations are unaffected;
- retains on independently identified allocations commute;
- retains and observations commute on **known-distinct allocations**;
- one retain can change the result of observing the *same* allocation;
- equal modeled event lists have equal modeled replay observations.

The modeled resource ID denotes an **allocation identity**, not a source
variable number. It omits failed operations, last-release destruction,
physical identities, sharing topology, arbitrary aliasing, closures,
callbacks and concurrent effects. The Rust receipt additionally records
`dec` and `del` for order preservation, but **the Lean model does not yet
prove their operational semantics or justify moving them**.

There is no Lean theorem that the actual Rust scanner implements the
event extraction semantics, or that `Reader::body` faithfully implements
the Lean C runtime; the latter requires a separate simulation. Tests only
establish behavior for exercised cases.

## Local evidence and reproduction

The two independent, local checks were run with the user's pinned toolchains:

```bash
/path/to/lean-4.34.1/bin/lean compiler/proofs/ReaderEffectOrder.lean
# Seven theorem receipts; no sorryAx.

/path/to/rust-1.99.1/bin/cargo test --offline \
  --manifest-path compiler/Cargo.toml effect_order
# Requires the full repository and native ABI build inputs.
```

Five standalone unit tests in `effect_order.rs` were also compiled and
passed with `rustc 1.99.1 --test` using a minimal module wrapper.
They cover valid order, reordering, deletion/insertion, operand or flag
changes, and unrecognized syntax. This tests the **pure verifier** only.

The integrated `scripts/check.sh` now includes an exact-head Lean
axiom receipt, and the already-existing source-native
`examples/ReferenceBookkeepingFixture.lean` checks the *actual Reader*
output for the accepted `isShared`-before-`inc` program. Its existing
negative source IR cases continue to refuse effect-before-observation.
**The entire compiler integration suite was not run in the local checkout
used to author this change**; exact-head CI is required before considering
the integration independently verified.

## Next proof obligations

1. Replace textual emitted-operation recognition with a small
   independently decoded generated-program AST, without a second emitter.
2. Formally relate source `FnBody` traversal to the Rust event decoder,
   with explicit proof coverage for joins, cases, direct/indirect calls,
   and reference alias relationships.
3. Extend Lean's model to release, shell-only delete, borrowing,
   object layout, destructor cascades, failure and admission.
4. Establish operational refinement to the actual pinned Lean C
   primitives and then independently to any Rust-native runtime.
5. Only after an alias/footprint proof, permit safe reordering of
   actual source effects. **This PR does not reorder anything.**

Related research:
[effect-aware optimization](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/concepts/compiler-effects-and-speculation.md)
and [compiler correctness methods](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/compiler-correctness-methods.md).
