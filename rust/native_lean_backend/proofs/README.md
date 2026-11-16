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
`rustc`'s execution of the emitted text. The separate Bool-source extension below covers that narrower branch fragment.
The
`Reader::decode`/FFI boundary, runtime reference counts, calls, joins and
remaining supported IR stay separate obligations.

## Original IR comparison and Bool branch semantics

[ReaderIRBoolSoundness.lean](ReaderIRBoolSoundness.lean) extends the
source-IR theorem to `UInt64.decEq`, `UInt64.decLt`, and
`UInt64.decLe` and both alternatives of a source `IR.FnBody.case`.

The accepted source fragment now has:
- Source-side big-step rules on actual `Lean.IR.Expr`, `FnBody` and
  `Alt.ctor` nodes; genuine `UInt64` comparison operators and
  branch-local environments.
- A total, fuel-bounded, proof-producing scanner which checks the complete
  pair of Bool constructors by original name and index, enforces
  `UInt8`-typed scrutinees and refuses unknown instructions or defaults.
- A compositional all-input `body_sound` theorem, including nested branches,
  and `reader_emission_and_ir_refine`, explicitly asserting **both** byte
  equality for the source produced by the production Reader FFI **and** the
  source-IR-to-modeled-target all-input value relation.
- Exact-head Lean CI tests for original compiled IR of `plus`,
  `straightChain`, `choose`, and `nested`; `subtract` stays a
  fail-closed negative. The axiom audit rejects `sorryAx`.

The semantics of the comparison-result variable here is modeled as a
Boolean selected by the actual `UInt64` comparison. Its correspondence to
Lean's physical `UInt8` storage layout and the C FFI representation is **not**
a proved low-level decoding theorem. Nor does text equality establish
`rustc`/MIR/machine execution equivalence. Calls, joins, RC effects, and
other IR instructions are outside this proof and must remain separate work.

## Borrowed C-backed IR decoder observation and UInt8 tags

[ReaderIRABIObservation.lean](ReaderIRABIObservation.lean) independently
renders the original `Lean.IR.Decl` structure for the source-certified scalar
and nested Bool fragment. The new native entry point
`NativeRust.scalarABIObserve` traverses that **same live borrowed original
object** using production Reader's `checked_tag`, `field`, `var`,
`array`, `ty`, `name` and `FnBodyView` accessors, backed by the pinned
`native/abi.c` shim. CI compares the complete structural readbacks.

The verified runtime observations include declaration and parameter layouts,
original source variable IDs, literal values, primitive names and operands,
`UInt8` cases, constructor names and exact 0/1 tags, case alternative order,
branch-local bodies and returns. Four positive original-IR fixtures are
checked. A reversed Bool alternative array must still agree. Three malformed
source IR values with duplicate, missing and default Bool alternatives must
fail closed in both the original-Lean reifier and native observer. Neither
path is allowed to execute malformed IR.

The separate Lean theorems `bool_byte_roundtrip`, `bool_byte_nat` and
`bool_byte_branch` establish the **abstract** valid `UInt8` tag
representation (false=0, true=1), its round trip and branch selection,
without axioms. These theorems do not depend on a physical pointer model.

**Important trust boundary:** this is live differential evidence for the
actual borrowed C/Rust decoder plus a kernel proof of the abstract tag
semantics. It is **not** a formal refinement proof of arbitrary Lean heap
objects through `lean.h`, `native/abi.c`, Rust unsafe reads or the Lean
runtime's physical tagged-value layout. Those remain explicitly open, as
does a `rustc` execution theorem.

## Imperative emitted Rust: semantics and actual rustc execution

The separate final-impure-LCNF capture check runs before this proof and remains
read-only; neither witness is allowed to change canonical Reader emission.

[ReaderRustStatement.lean](ReaderRustStatement.lean) adds a target operational
model of the **imperative statements Reader emits**, not another evaluation
of the prior expression tree. It distinguishes typed `u64` and `u8`
bindings, named registers, wrapping addition and multiplication, comparisons
encoded as 0/1 tags, branch-local `match` arms and variable returns.

The target `Runs` relation uses a separate register environment and
explicit wrapping modulo `2^64`. A proof-producing, fuel-bounded checker
constructs `StmtMatches` only for known instructions and existing operand
bindings. Its canonical complete Rust function text must match the **actual**
production Reader output byte for byte. Certification also requires the
already-established source-IR semantics and live C-backed decoder readback.

The all-input `statement_sound` theorem proves execution of every witnessed
imperative target block according to the existing modeled Rust value
semantics. `original_ir_and_emitted_rust_agree` combines the *original*
Lean.IR big-step source execution with the imperative target execution,
in one theorem for every pair of `UInt64` inputs. The exact Reader-source
and live-ABI-observation equalities are explicit in the conclusion.
Both theorems are kernel-checked under Lean 4.34.1, with only `propext`.

Separately, native CI writes the **unchanged certified Reader functions**
as Rust source, appends only an input/output driver, and executes them using
the pinned real `rustc`. It tests `opt-level=0` and `opt-level=3` with
overflow checking enabled, using 612 input pairs per original source
definition (100 boundary pairs and 512 seeded pseudorandom pairs). The
four source functions cover literal/add/mul, equality and ordering, both
branch outcomes, and nested branches. `UInt64.sub` remains explicitly
refused by the certified language even though general Reader supports it.
There are 4,896 independent original Lean oracle comparisons.

The native workflow retains `reader-rust-execution-receipt.txt`, the proof
axiom output, exact generated Rust function source plus driver, oracle
inputs, expected values, and observed unoptimized/optimized outputs. The
receipt pins the Git revision, toolchain versions and source SHA-256 digests.

**Unproved machine boundary:** `RustStatement.Runs` is a separately modeled
semantics for a *restricted Rust statement grammar*, not a mechanized
semantics of the real Rust parser, borrow checker, MIR, optimizer, or CPU.
Finite `rustc` oracle comparisons test the real execution path, but do
not establish universal compiler correctness. Native reference-count
ownership, calls, joins, mutation, all remaining supported IR and G2 ETH
source-program execution remain separate.

## Unproved obligations for a real G1 compiler theorem

1. Prove that `Reader::decode` and `Reader::view` faithfully read and validate
   actual Lean 4.34.1 compiler IR nodes and their types, including rejected IR.
2. Generalize the new exact-emission certificate beyond its restricted scalar
   fragment and prove the independent IR reifier/typed target rendering
   relation compositionally. The general Reader `String` emitter is still
   unverified.
3. Extend the now kernel-checked **restricted imperative Rust statement**
   execution model beyond scalar/Bool IR, and establish an independently
   checked `rustc` parsing-to-MIR or machine-code semantics correspondence.
   Existing real-`rustc` oracle executions are tests, not that theorem.
4. Generalize from a finite arithmetic/branch tree to lexical environments,
   joins, direct/indirect calls, recursion, allocation, closures, borrowing,
   mutations and physical reference counts. No general ownership theorem exists.
5. Establish a refinement *for the exact supported language*, with rejection
   correctness and resource correspondence as distinct statements.
6. Treat G2's source-defined noncomputable ETH program separately.

No hypothetical theorem above may be marked proved merely by a passing
differential fixture. CI kernel-checks the model theorem under Lean 4.34.1,
and `scripts/check.sh` runs the check before native compiler conformance.
