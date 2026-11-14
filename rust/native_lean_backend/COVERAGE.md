# Native IR coverage contract (Lean 4.34.1)

This is a **strictly bounded executable subset**, not a complete Lean compiler.
Any unlisted IR variant, primitive, runtime dependency or program shape must
refuse. Constructor/tag identities below are pinned to
`Lean/Compiler/IR/Basic.lean` at Lean commit
`5045d0056413266e57c625dcd7c365b10e377c52`.

| IR family | Supported | Explicitly unsupported |
| --- | --- | --- |
| `Decl` | `fdecl` (chosen root and reachable executable dependencies, including imported IR) | unsupported `extern` dependencies |
| `IRType` | `uint8`, `uint16`, `uint32`, `uint64`, `usize`; bounded immutable `object`, `tobject`, `tagged` | `float`, `float32`, `erased`, `void`, `struct`, `union`; unrestricted object semantics |
| `Arg` | `var` with known, matching type | `erased` in runtime position |
| `Expr` | bounded `lit.num`, registered direct `fap`, exact immutable `Option`/`Prod` `ctor`/`proj`, fixed-width `box`/`unbox`, statically compiled boxed `pap`/`ap` | `reset`, `reuse`, `uproj`, `sproj`, `lit.str`, `isShared`, unverified constructor/closure layouts, other `fap` |
| `FnBody` | `vdecl`, `ret`, exact Bool/Option `case`, nonrecursive typed joins, and immutable-only `inc`/`dec`/`del` bookkeeping | recursive joins, mutable `set`/`setTag`/`uset`/`sset`, observable RC, other `case`, `unreachable` |
| `Alt` | two exact Bool/Option `ctor` alternatives | `default`, unknown constructor layouts |
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

## Extension: join points and multiple public roots

- The native emitter recognizes `FnBody.jdecl` and `FnBody.jmp` for **lexical,
  non-recursive scalar joins**. It validates parameter types and jump argument
  arity; join bodies cannot recursively reference their own join identifier.
  Multiple Boolean arms have independent variable/type scopes.
- `#native_rust_package [RootA.name, RootB.name] to "new/path"` emits a
  standalone Rust Cargo **library** (not a binary), deduplicating the union of
  reachable compiled dependencies. Public functions use each final Lean name
  component. Identical public names are rejected before publishing.
- The generated crate contains `[workspace]` in Cargo.toml so its build does
  not unintentionally become a member of the generating compiler workspace.
- Clean build: 1,984 prior closure/scalar comparisons, 256 join-point
  comparisons, 768 Cargo-package comparisons: **3,008** total. Neither the
  general control-flow completion gate nor general data/runtime semantics is
  established by this subset.

## Source-derived constructor inventory (integration of PR #200)

`scripts/VerifyIRInventory.lean` asks the **actual pinned Lean 4.34.1 environment** for constructor identities and order in `Decl`, `IRType`, `Arg`, `LitVal`, `Expr`, `Alt`, and `FnBody`. `scripts/check.sh` runs this inspection **before native codegen** and fails if a pinned IR family has changed. It emits `artifacts/ir-coverage.tsv` and includes its SHA-256 and the generator SHA-256 in the smoke receipt. Exactly 30 selected typed binary primitives are recorded; all others remain refused. `FnBody.jdecl` and `FnBody.jmp` are marked *conditional* only for the scoped nonrecursive scalar joins exercised in this branch.

This inventory is a constructor **membership/order** check, not a complete ABI layout audit or proof of Rust semantic correspondence. No duplicate `#native_rust_bundle` route is added: `#native_rust_package` remains the one multi-root Cargo-producing interface, with real Lean/Rust join and three-root differential fixtures. The imported subset claims only what the combined smoke actually tests; G1 requirements 13, 23, 29 and release 41 remain open.

## Runtime-gated IR whitelist and primitive matrix (#201 integration)

The real pinned Lean 4.34.1 constructor inventory is first checked by `scripts/VerifyIRInventory.lean` and recorded in `artifacts/ir-constructor-summary.tsv`. Separately, `examples/IRInventory.lean` and `scripts/coverage-ledger.rs` verify the complete 48-constructor tag classification, publishing `artifacts/ir-constructors.tsv` and `artifacts/ir-coverage.tsv`. The Rust `build.rs` compiles the same checked classification into `SUPPORTED_IR_TAGS`, and **production readers refuse unclassified tags**.

Of those 48 constructors, **28** are bounded-supported, including nonrecursive typed `FnBody.jdecl`/`FnBody.jmp`, validated immutable objects and source-defined boxed `Expr.pap`/`Expr.ap`. The other **20** are explicitly unsupported. No unsupported branch is allowed to become accepted just because a Rust `match` arm is added. The `primitive-registry.tsv` is now the production lookup for exactly 30 typed unsigned operations. A generated 30 × 64 matrix of independent original-Lean results (1,920 comparisons) is executed from source IR. The integrated suite covers **13,336** original-Lean/Rust fixture comparisons (3,008 scalar/join/multi-root, 3,072 immutable Option/Prod, 2,048 boxed functions, and 5,208 GMP-backed Nat), plus a separately recorded 1,920-comparison fixed-width primitive matrix. These checks do **not** establish arbitrary Lean collections, general Nat/Int, effects, or whole ETH-source compilation.

## Integrated immutable object and callable subset

IRType.object/tobject/tagged and the supported Expr.ctor/proj/box/unbox
forms are accepted only for verified immutable Option/Prod layouts.
Expr.pap and Expr.ap accept statically compiled, source-defined
all-boxed call signatures and preserve captured values in immutable Rc
objects. FnBody.inc/dec/del are non-observable only while mutation,
reuse/reset/isShared and unknown heap layouts are prohibited.
Source-differential evidence: 3,072 object + 2,048 callable results.

## GMP Nat exact operation subset

Nat.add/sub/mul/div/mod/decEq/decLt/decLe are recognized only
with actual pinned compiler IR and known object/scalar return types.
Generated Rc-backed Nat values store arbitrary-precision GMP integers.
Lean Nat subtraction is saturating, and division/remainder by zero
are total. All other Nat primitives refuse (including Nat.land).
The original Lean runtime supplies 5,208 numerical oracles with
0 to 1024-bit inputs; no machine-width truncation or synthesized
finite-table implementation is accepted. GMP must be installed on
supported Linux x86-64 execution hosts; no Lean runtime is linked.

### Canonical runtime across Nat, Option/Prod and first-class closures

The current pinned G1 generator embeds a **single source of truth** for the entire supported immutable object, GMP-backed Nat and boxed closure representation: `src/runtime/immutable_value.rs`, loaded with `include_str!`. Its 9,786 source bytes are identical to the previously tested inline `RUNTIME_SOURCE` after PR #209. The native smoke gate now verifies that the generated Object, Function and Nat Cargo packages all begin with those **exact bytes**, each containing exactly one `__LeanValue` and `__LeanValueRepr` declaration. The receipt hashes this source independently of generated code. This does not add an alternative runtime or compiler.

`Rc` immutable values use tagged nullary values, fixed-width boxed scalars, verified pointer-only constructors, source-defined closure captures/thunks and source-refined GMP naturals. Lean `inc/dec/del` bookkeeping can be erased only while `isShared`, `reset`, `reuse`, mutation and unverified layouts remain forbidden. The emitted model does **not** reproduce arbitrary physical Lean heap/RC semantics.

The three original unmodified source probes (Newspeak, Armada, Keboola) pass Lean build and original Lean oracle checks, but still refuse Rust extraction at `Expr.isShared`, external `Nat.decLe`, and `Expr.sproj`, respectively. Item [#193-32](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/193) remains open. The pending [#219](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/219) Int/String/Array work must **extend** the canonical `__LeanValue` representation and preserve this three-crate identity check, not add a competing Value runtime.
