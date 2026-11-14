# Native IR coverage contract (Lean 4.34.1)

This is a **strictly bounded executable subset**, not a complete Lean compiler.
Any unlisted IR variant, primitive, runtime dependency or program shape must
refuse. Constructor/tag identities below are pinned to
`Lean/Compiler/IR/Basic.lean` at Lean commit
`5045d0056413266e57c625dcd7c365b10e377c52`.

| IR family | Supported | Explicitly unsupported |
| --- | --- | --- |
| `Decl` | `fdecl` (chosen root and reachable executable dependencies, including imported IR) | unsupported `extern` dependencies |
| `IRType` | `uint8`, `uint16`, `uint32`, `uint64`, `usize`, plus bounded `object`/`tobject`/`tagged` value adapters | `float`, `float32`, `erased`, `void`, `struct`, `union` and arbitrary heap layouts |
| `Arg` | `var` with known type; `erased` only in exact Array type-proof positions | erased values used as runtime operands |
| `Expr` | bounded `lit.num`, selected `fap` primitives, typed direct calls, UInt64-to-value `box` | `ctor`, `reset`, `reuse`, `proj`, `uproj`, `sproj`, `pap`, `ap`, other `box`/`unbox`, `lit.str`, `isShared`, other `fap` |
| `FnBody` | `vdecl`, `ret`, `case` on Bool-as-UInt8 with exactly `Bool.false` and `Bool.true` arms | `jdecl`, `jmp`, `set`, `setTag`, `uset`, `sset`, `inc`, `dec`, `del`, other `case`, `unreachable` |
| `Alt` | two exact Bool `ctor` alternatives | `default`, other constructors |
| Primitive operations | 30 scalar operations plus ten exact Nat/Int/String/Array/List value adapters in `runtime-primitive-registry.tsv` | all other runtime calls |

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
- `scripts/check.sh` compiles 15 isolated declarations **and three additional
  closure roots**, including a separately compiled imported module, shared
  diamond dependencies, direct recursion and mutual recursion; all generated
  Rust compiles and executes against **1,984 independent assertions**
  evaluated by original Lean definitions on fixed edges and seeded vectors.
- Run `lake build` and `scripts/check.sh` from a clean checkout. The separate
  `native-lean-rust.yml` job targets PR changes in this subtree and logs an
  exact-head receipt with source hashes and generated-Rust hashes.

Tests establish coverage of these examples, **not a universal semantic
refinement theorem**. For expanded coverage, see tracking issue #193. The
separate ETH symbolic/physical semantics obligations remain open.

## Closure compilation boundary (new)

- `#native_rust_closure` collects original executable IR transitively through
  `Lean.Compiler.compile` and `Lean.IR.findDecl`, including dependencies stored
  in previously compiled `.olean` modules. It passes a live, borrowed
  `Array Lean.IR.Decl` to the Rust `cdylib`, **without JSON**.
- Rust independently deduplicates and traverses reachable functions, validates
  each signature and direct call, and writes stable collision-free internal
  Rust names based on full Lean names. Calls may form cycles.
- A reachable missing declaration, `extern` lacking a supported exact
  implementation, unsupported body, unsupported primitive, or `sorryAx`
  dependency **refuses the whole closure** without publishing partial code.
- Compilation is deterministic on repeated runs; imported shared dependencies
  are emitted exactly once. This is **one named root per emission**, not yet
  a complete Cargo crate or arbitrary project build.
- Lean names are currently accepted only when every component is an
  unambiguous ASCII identifier. Numeric and quoted/special components refuse
  rather than potentially aliasing distinct Lean declaration identities.
- Only typed, fully applied, direct calls to emitted functions are supported;
  indirect applications, closures, join points, and general runtime types
  remain unsupported. Recursive functions with supported bodies compile, but
  no guarantee of stack safety or tail-call optimization is claimed.


## Native response and publication contract (G1 hardening)

The compiler now reports supported-IR refusals as a JSON object following
the `ERROR\n` prefix. Fields: `status`, `declaration`, `construct`, `reason`.
A native C ABI host-runtime probe verifies small tagged scalars, a two-field
constructor, and Lean String operations before lowering. Rust codegen has an
explicit per-body traversal/time budget and a 4 MiB output cap. Output paths
are validated and staged adjacent to the destination for atomic rename.

A generated supported root may be packaged into a standalone Cargo library
with `scripts/package_crate.sh`, then built/tested without Lean runtime
environment variables. This does not yet implement compiler-native
multi-root crate generation. See [SAFETY.md](SAFETY.md) for the full trust
boundary and remaining checklist items 21–30. In particular, a comprehensive
automatically-derived conformance matrix is still open.

## Derived constructor and primitive conformance

The pinned Lean environment emits a constructor inventory which must exactly
match `ir-coverage-classification.tsv`. Rust `build.rs` converts the 19
`implemented_bounded` entries into the production decoder's allowed tag set;
all other constructor variants fail closed. `primitive-registry.tsv` is the
shared production primitive list, not a parallel prose table. The native
smoke suite generates 1,920 extra original-Lean oracle checks (30 primitives ×
64 inputs), alongside the existing 1,984, and verifies exact-source receipts.

[CONFORMANCE.md](CONFORMANCE.md) describes the machine-readable ledgers,
coverage scope, and what testing does *not* establish.

## Item 30 object-value conformance

Ten source-native primitive adapters provide exact BigNat/BigInt arithmetic,
Unicode append/length, Array UInt64 push/size and List UInt64 reversal.
The bounded whitelist now allows 19 of 48 IR constructors and refuses 29.
The new original-Lean oracle fixture adds **101 comparisons**, yielding
**4,005** total across the historical scalar/control-flow/recursion suite.
Undefined/unimplemented heap operations are not silently substituted.
See [SEMANTICS.md](SEMANTICS.md) for the type boundary and exact evidence.
