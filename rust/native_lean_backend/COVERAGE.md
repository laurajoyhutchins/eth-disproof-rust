# Native IR coverage contract (Lean 4.34.1)

This is a **strictly bounded executable subset**, not a complete Lean compiler.
Any unlisted IR variant, primitive, runtime dependency or program shape must
refuse. Constructor/tag identities below are pinned to
`Lean/Compiler/IR/Basic.lean` at Lean commit
`5045d0056413266e57c625dcd7c365b10e377c52`.

| IR family | Supported | Explicitly unsupported |
| --- | --- | --- |
| `Decl` | `fdecl` (chosen root and reachable executable dependencies, including imported IR) | unsupported `extern` dependencies |
| `IRType` | `uint8`, `uint16`, `uint32`, `uint64`, `usize`, plus `object`, `tobject`, `tagged` for the verified immutable runtime | `float`, `float32`, `erased`, `void`, `struct`, `union` |
| `Arg` | `var` with known, matching type | `erased` in runtime position |
| `Expr` | bounded `lit.num` (including large boxed Nat literals <= 4 KiB), selected `fap` primitives and typed direct calls; immutable `Option.none`, `Option.some`, `Prod.mk` constructors, `box`, `unbox`, object `proj` | `reset`, `reuse`, `uproj`, `sproj`, `pap`, `ap`, `lit.str`, `isShared`, unverified constructors, other `fap` |
| `FnBody` | `vdecl`, `ret`, Bool cases, `Option.none`/`Option.some` cases, nonrecursive `jdecl`/`jmp`, object-only `inc`/`dec`/`del` erased under immutable `Rc` ownership | `set`, `setTag`, `uset`, `sset`, other `case`, `unreachable`, recursive joins |
| `Alt` | two exact Bool alternatives or two exact `Option` constructors | `default`, other constructors |
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

## Extension: immutable object values (stacked PR following #202)

- Compiler IR `object`, `tobject` and `tagged` map to a small generated Rust
  `Rc`-backed immutable value representation. Supported constructor layouts
  are exactly `Option.none` (tagged), `Option.some` (one pointer field) and
  `Prod.mk` (two pointer fields). Metadata (index, pointer count and scalar
  layout) is checked before generation. Unsupported constructors refuse.
- `Expr.box` and `Expr.unbox` preserve their fixed-width scalar payload types.
  `Expr.proj` clones immutable constructor fields, preserving sharing.
  Output is standalone Rust with no Lean runtime and no third-party crates.
- `FnBody.inc`, `dec`, and `del` are eliminated for these immutable values
  because Rust `Rc` ownership replaces source refcount bookkeeping. **This is
  valid only while** `reset`, `reuse`, `isShared`, and mutation instructions
  remain unsupported. They must not be enabled independently.
- For object-valued case scrutinees, `Option.none` and `Option.some` tags and
  exact constructor names and layouts are checked. Other ADTs and default
  alternatives refuse. Root functions in the integration suite use *scalar*
  public APIs, so no general source-level ADT type mapping is claimed.
- `examples/Objects.lean` builds three interconnected roots containing nested
  Options and pairs. It checks 3,072 original-Lean-evaluated results on edges
  and seeded vectors. `RefusalObjectNat.lean` and `RefusalObjectCtor.lean`
  prove that arbitrary-precision `Nat` and unknown `Sum` layouts still fail
  closed without publishing a Cargo package.
- Total smoke suite: **6,080** differential assertions, not a general
  semantic-refinement theorem. Arbitrary-precision Nat, String, Array, and
  mutable object semantics remain entirely unsupported.

## Extension: GMP-backed arbitrary-precision Nat (post #204)

- When Nat operations are reachable, the generated immutable runtime
  includes a GMP-backed Nat variant; tagged small Nat literals and boxed arbitrary-width inputs share
  the same operation semantics. Nat never silently truncates to machine word.
- Implemented exact native primitive lowering: `Nat.add`, `Nat.sub`,
  `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.decEq`, `Nat.decLt`, `Nat.decLe`.
  `Nat.sub` is truncated at zero. Both `Nat.div` and `Nat.mod` have explicit
  Lean-compatible zero-divisor semantics.
- All remaining Nat primitives (including non-folded `Nat.pow`),
  unimplemented field layouts and unsupported object shapes refuse.
  Large **decimal literal** constants are supported via the pinned Lean runtime
  up to a 4 KiB bigint storage cap; nonliteral expressions are not implicitly
  constant-folded or substituted.
- Integration suite: 5,208 original Nat assertions on up-to-1,024-bit inputs,
  plus 76 new large-literal assertions and the preceding 6,080 case suite.
  **11,364 total**. This is
  empirical semantics checking, **not** a proof of full Lean compiler or
  kernel-to-machine-code correctness.
- GMP is now emitted and linked **only for generated code with Nat primitive
  operations or boxed Nat literals**. Constructor-only object programs have
  no GMP dependency, verified against linked Cargo test executables. Generated
  code does not depend on Lean at runtime, but bigint programs still depend
  on GMP. The 4 KiB constant bound prevents unbounded quadratic decimal
  conversion in the pinned Lean C ABI shim.

## Extension: immutable copy-on-write Array values

- Implemented pinned native Array FFI-call identities: `Array.mkEmpty`,
  `Array.push`, `Array.size`, `Array.getInternal`,
  `Array.getInternalBorrowed`, and `Array.set!`.
- Each primitive enforces an exact arity, result IR type, erased argument
  positions, and source type categories. Index operands must be statically
  `tagged` Nat; arbitrary boxed `Nat` indices **refuse**.
- `Nat.decEq`/`decLt`/`decLe` on two statically tagged values use host
  `usize` comparisons, avoiding GMP for pure tagged-Array programs.
- Array updates return new vectors, preserving prior values on branches and
  under `Rc` sharing. This is extensional value semantics, not an exact model
  of Lean's mutable storage allocation or primitive TM2 costs. Current writes
  copy O(n) elements and repeated pushes can take O(n²) time.
- `examples/ArrayFixture.lean` compiles five roots and compares 1,280
  independently Lean-evaluated results. A generated Cargo executable has no
  GMP or Lean dynamic-library dependency. Both generated source determinism
  and unsupported `Array.pop`/`Array.get!Internal` refusals are checked.
- Full local smoke expectation: **12,644** differential assertions across
  all preceding compiler fixtures and the Array extension. No general array
  API, arbitrary-size source program, mutation ownership equivalence, or
  proof of semantic refinement is implied.
