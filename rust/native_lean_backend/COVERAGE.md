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
| `Expr` | bounded `lit.num`, registered direct `fap`, exact immutable `Option`/`Prod` `ctor`, typed `proj`, fixed-width `box`/`unbox` | `reset`, `reuse`, `uproj`, `sproj`, `pap`, `ap`, `lit.str`, `isShared`, unknown constructors, other `fap` |
| `FnBody` | `vdecl`, `ret`, exact Bool/Option `case`, bounded nonrecursive typed joins, immutable-only `inc`/`dec`/`del` bookkeeping | recursive joins, mutations `set`/`setTag`/`uset`/`sset`, unrestricted reference-count observability, other cases, `unreachable` |
| `Alt` | two exact Bool or Option `ctor` alternatives | `default`, unknown constructor layouts |
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

Of those 48 constructors, **26** are bounded-supported, including `FnBody.jdecl` and `FnBody.jmp` strictly for nonrecursive typed lexical joins and ten newly gated immutable-object constructors. The other **22** are explicitly unsupported. No unsupported branch is allowed to become accepted just because a Rust `match` arm is added. The `primitive-registry.tsv` is now the production lookup for exactly 30 typed unsigned operations. A generated 30 × 64 matrix of independent original-Lean results (1,920 comparisons) is executed from source IR. The original fixture gate covers 3,008 base/join/multi-root comparisons; an additional 3,072 original-Lean evaluations verify the bounded immutable Option/Prod runtime (6,080 in total). These checks do **not** establish semantic correctness of general collections, arbitrary-precision `Nat`/`Int`, effects, or whole ETH-source compilation.

## One immutable runtime, with explicit extension seams

The production compiler embeds **one canonical source**, `src/runtime/immutable_value.rs`, using Rust `include_str!` from the in-process backend. Generated Cargo programs receive an `Rc`-backed `__LeanValue` only if their emitted source uses that value type. The current representation distinguishes tagged nullary values, typed boxed fixed-width scalars and constructors with validated pointer-only fields. The original Lean IR supplies executable bodies, constructor identities, arities and layout metadata. An unknown field layout always refuses; no host algorithm substitutes for Lean.

**Ownership:** `inc`, `dec` and `del` may be erased only because the accepted objects are immutable and `isShared`, `reset`, `reuse` and mutation are all refused. The emitted object is an owned Rust `Rc` value; there are no borrowed Lean runtime pointers in a standalone executable. This does **not** prove physical Lean RC equivalence, pointer identity equivalence, or behavior of user programs that observe sharing.

**Source-specific negative coverage:** the immutable pinned three-project acceptance matrix (draft [#213](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/213)) builds and checks Newspeak, Armada and Keboola unchanged. After integrating the bounded object runtime, the [#215 exact-head native run](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43616990857) refuses Newspeak at `Expr.isShared`, Armada at extern `Nat.decLe`, and Keboola at `Expr.sproj`. These are deliberate **fail-closed** boundaries, not three successful Rust compilations. Item #193-32 remains open.

**Runtime branch reconciliation:** this represents the tested immutable foundation of [#204](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/204), but it is *not* a silent merge of #204's older emitter or publication paths. [#210](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/210) (source-defined closures) and [#209](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/209) (GMP-backed Nat) should extend the single generated runtime and preserve the current whitelist and publisher. The competing [#205](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/205) broad value runtime cannot be merged as an independent second `Value` ABI; its tested semantics must be reconciled feature-by-feature. A runtime with mixed heap/RC/mutable semantics remains unsupported until source-equivalent tests and precise ownership rules exist.
