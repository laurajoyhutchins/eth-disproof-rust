# Native IR coverage contract (Lean 4.34.1)

This is a **strictly bounded executable subset**, not a complete Lean compiler.
Any unlisted IR variant, primitive, runtime dependency or program shape must
refuse. Constructor/tag identities below are pinned to
`Lean/Compiler/IR/Basic.lean` at Lean commit
`5045d0056413266e57c625dcd7c365b10e377c52`.

| IR family | Supported | Explicitly unsupported |
| --- | --- | --- |
| `Decl` | `fdecl` (one chosen root) | `extern`, transitive root closure |
| `IRType` | `uint8`, `uint16`, `uint32`, `uint64`, `usize` | `float`, `float32`, `erased`, `object`, `tobject`, `tagged`, `void`, `struct`, `union` |
| `Arg` | `var` with known, matching type | `erased` in runtime position |
| `Expr` | bounded `lit.num`, selected `fap` primitives | `ctor`, `reset`, `reuse`, `proj`, `uproj`, `sproj`, `pap`, `ap`, `box`, `unbox`, `lit.str`, `isShared`, other `fap` |
| `FnBody` | `vdecl`, `ret`, `case` on Bool-as-UInt8 with exactly `Bool.false` and `Bool.true` arms | `jdecl`, `jmp`, `set`, `setTag`, `uset`, `sset`, `inc`, `dec`, `del`, other `case`, `unreachable` |
| `Alt` | two exact Bool `ctor` alternatives | `default`, other constructors |
| Primitive operations | `UInt8/16/32/64` and `USize` `.add`, `.sub`, `.mul`, `.decEq`, `.decLt`, `.decLe` | all other runtime calls |

**Semantic restrictions:** scalar inputs/outputs use Rust integer representations;
Lean `Bool` is emitted as the compiler's `u8` representation (`0=false`,
`1=true`). Bool-pattern matching assumes valid Lean Bool tags. Fixed-width
arithmetic wraps; comparison outputs are `u8::from(bool)`. A constant is
accepted only if it fits its declared result type and its source numeric
value is a Lean tagged small `Nat` (large literals refuse).

## Validation requirements

- Build-time Lean **version and exact compiler commit** check; Linux x86-64
  only for this version.
- No JSON IR or source parser. A borrowed `Lean.IR.Decl` crosses directly into
  the native Rust backend via the pinned C ABI accessor shim.
- Variable types, primitive namespaces and result types checked before
  emission; duplicate or unknown variables refuse.
- Unsupported branches, runtime types, bad output identifiers, and wrong
  primitive shapes refuse; the public Lean command must not modify a previous
  output on refusal.
- `scripts/check.sh` compiles 15 actual Lean declarations, generates Rust,
  compiles and executes the result, and checks **1,600 independent assertions**
  evaluated by original Lean definitions on fixed edges and seeded vectors.
- Run `lake build` and `scripts/check.sh` from a clean checkout. The separate
  `native-lean-rust.yml` job targets PR changes in this subtree and logs an
  exact-head receipt with source hashes and generated-Rust hashes.

Tests establish coverage of these examples, **not a universal semantic
refinement theorem**. For expanded coverage, see tracking issue #193. The
separate ETH symbolic/physical semantics obligations remain open.
