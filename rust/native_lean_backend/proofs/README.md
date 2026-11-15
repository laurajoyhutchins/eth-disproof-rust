# G1 operational refinement: first executable-IR fragment

**Status:** The kernel theorem covers an independent mathematical model of a
subset of the Lean compiler's supported scalar IR. It is not a theorem about
the entire Rust emitter or its physical execution.

## Theorem and exact source connection

[ScalarOperationalRefinement.lean](ScalarOperationalRefinement.lean) proves,
for every input environment and every finite syntax tree in its grammar,

```
evalRustProgram (fun i => (env i).val) program
  = (evalSourceProgram env program).val
```

The first source model uses `Fin (2^64)` arithmetic. A second, stronger
source bridge uses the **actual Lean `UInt64` operations**, with Lean's pinned
`UInt64.toNat_add`/`toNat_mul` theorems, and proves the same all-input program
result for genuine `UInt64` inputs and comparisons. The independently defined
target uses natural-number arithmetic reduced modulo `2^64`, the intended
semantics of Rust's wrapping operations. The grammar has `arg`, `lit`, `add`, `mul`,
`eq`, `lt`, `le`, `return` and nested conditional branches.

The proof now also includes a **distinct target AST** (`RustExpr`,
`RustCompare`, `RustProgram`) and a total `lowerProgram` function.
`modeled_compiler_refines` composes the model-lowering theorem with the
genuine Lean `UInt64` source theorem, for all modeled programs and inputs.
The target grammar models `wrapping_add`, `wrapping_mul`, scalar comparisons,
`u8` Bool tags, and branch selection. **This is not the production Rust text
emitter.**

The correspondence being audited is specifically:

| Source operation | `primitive-registry.tsv` | Rust emission in `src/reader/expr_call.rs` |
| --- | --- | --- |
| `UInt64.add` | `u64\twrapping_add` | `{lhs}.wrapping_add({rhs})` |
| `UInt64.mul` | `u64\twrapping_mul` | `{lhs}.wrapping_mul({rhs})` |
| `UInt64.decEq` | `u64\t==` | `u8::from({lhs} == {rhs})` |
| `UInt64.decLt` | `u64\t<` | `u8::from({lhs} < {rhs})` |
| `UInt64.decLe` | `u64\t<=` | `u8::from({lhs} <= {rhs})` |

The existing original-Lean-to-Rust differential suite tests actual generated
Rust, but those tests do not discharge the link between the modeled target
semantics and `rustc` execution.


## Reader-to-target emission check

[ReaderScalarCertificate.lean](ReaderScalarCertificate.lean) independently
reifies the **actual** pinned \`Lean.IR.Decl\` for a narrower executable subset,
then invokes the real in-process Reader FFI. It constructs (1) the
\`ScalarOperationalRefinement.Program\` used by the all-input theorem and
(2) the complete canonical Rust function text, and accepts a certificate
only when Reader's entire output is equal to the independently rendered
source. There is no parallel production emitter or serialized-IR substitute.

The certified subset is UInt64 parameters and return, UInt64 literals,
\`UInt64.add\`/\`UInt64.mul\`, \`UInt64.decEq\`/\`decLt\`/\`decLe\`,
\`vdecl\`, \`ret\`, and two-constructor Bool \`case\` (including nesting).
The checker rejects direct calls, join points, subtraction, ownership
effects, object types, and every unsupported form. CI exercises three
original-Lean source programs and one explicit subtraction refusal.

This closes the **checked source-text equality** step for successfully
certified examples, not the full compiler-correctness theorem:
- The independent IR reifier's correspondence with an operational model of
  *all* admitted source IR has not been proved.
- The canonical Rust syntax's correspondence with \`rustc\`/MIR execution
  has not been proved.
- General Reader output outside this narrower grammar has no certificate.
- Physical reference-count ownership, calls, joins, and remaining IR are
  still distinct obligations.

A passing finite fixture alone is not the claim. A \`Certificate\` carries
exact Rust-source equality, while \`certified_model_refines\` applies the
existing all-input semantic theorem to the reified program. The trusted
boundary and conditional nature of the claim must remain explicit.

## Straight-line source-IR operational correspondence

[ReaderIRSoundness.lean](ReaderIRSoundness.lean) adds an independent big-step
source semantics over the actual pinned `Lean.IR.Expr` and
`Lean.IR.FnBody` constructors, including real Lean `UInt64` literal,
addition, and multiplication operations, environment updates and returns.

`ExprMatches` and `BodyMatches` are proof-carrying relations between those
real IR nodes and the modeled `WordExpr`/`Program`. The theorem
`body_sound` states, for **every** input and agreeing variable environment,
that a witnessed straight-line original IR body evaluates to the model result.
The `LinkedCertificate` additionally requires the independently constructed
Reader emission certificate to agree on the *same* modeled program.
`linked_reader_refines` composes these results for all input words.

The witness-producing scanner is a **total**, fuel-bounded checker, not an
unrestricted partial proof generator. CI uses original compiled Lean IR for a
direct addition and a chained literal/add/mul program, and checks that
subtraction and branching are refused by this narrower source proof path.
The native CI log prints the axioms of the compositional theorems and rejects
`sorryAx`.

This is not yet a proof that arbitrary real Lean IR executes correctly under
the independently specified source operational rules, nor a proof about
`rustc`'s execution of the emitted text. It also does not extend the
source-IR proof to the previously emission-certified Bool branches. The
`Reader::decode`/FFI boundary, runtime reference counts, calls, joins and
remaining supported IR stay separate obligations.

## Unproved obligations for a real G1 compiler theorem

1. Prove that `Reader::decode` and `Reader::view` faithfully read and validate
   actual Lean 4.34.1 compiler IR nodes and their types, including rejected IR.
2. Generalize the new exact-emission certificate beyond its restricted scalar
   fragment and prove the independent IR reifier/typed target rendering
   relation compositionally. The general Reader `String` emitter is still
   unverified.
3. Connect Rust execution to these target semantics, either through a trusted
   Rust operational model or an independently checked source-to-bytecode bridge.
4. Generalize from a finite arithmetic/branch tree to lexical environments,
   joins, direct/indirect calls, recursion, allocation, closures, borrowing,
   mutations and physical reference counts. No general ownership theorem exists.
5. Establish a refinement *for the exact supported language*, with rejection
   correctness and resource correspondence as distinct statements.
6. Treat G2's source-defined noncomputable ETH program separately.

No hypothetical theorem above may be marked proved merely by a passing
differential fixture. CI kernel-checks the model theorem under Lean 4.34.1,
and `scripts/check.sh` runs the check before native compiler conformance.
