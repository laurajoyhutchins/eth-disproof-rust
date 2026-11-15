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

## Unproved obligations for a real G1 compiler theorem

1. Prove that `Reader::decode` and `Reader::view` faithfully read and validate
   actual Lean 4.34.1 compiler IR nodes and their types, including rejected IR.
2. Make the implemented expression lowering produce a typed witness that each
   generated Rust operation matches the target operation interpreted here. The
   current `String` emitter does not create such a proof certificate.
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
