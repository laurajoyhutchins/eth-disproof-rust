# Native IR coverage contract (Lean 4.34.1)

This is a **strictly bounded executable subset**, not a complete Lean compiler.
Any unlisted IR variant, primitive, runtime dependency or program shape must
refuse. Constructor/tag identities below are pinned to
`Lean/Compiler/IR/Basic.lean` at Lean commit
`5045d0056413266e57c625dcd7c365b10e377c52`.

| IR family | Supported | Explicitly unsupported |
| --- | --- | --- |
| `Decl` | `fdecl` (chosen root and reachable executable dependencies, including imported IR) | unsupported `extern` dependencies |
| `IRType` | `uint8`, `uint16`, `uint32`, `uint64`, `usize`; `float` only for finite arithmetic; `tagged` only for nullary scalar enum | `float32`, `erased`, `object`, `tobject`, `void`, `struct`, `union`; other `float`/`tagged` shapes |
| `Arg` | `var` with known, matching type | `erased` in runtime position |
| `Expr` | bounded `lit.num`, selected `fap` primitives, typed direct calls, nullary scalar `ctor` | heap `ctor`, `reset`, `reuse`, `proj`, `uproj`, `sproj`, `pap`, `ap`, `box`, `unbox`, `lit.str`, `isShared`, other `fap` |
| `FnBody` | `vdecl`, `ret`, typed scalar `case` on Bool/finite nullary inductives, non-recursive scalar `jdecl`/`jmp` | recursive/general joins, `set`, `setTag`, `uset`, `sset`, `inc`, `dec`, `del`, heap `case`, `unreachable` |
| `Alt` | exact Bool `ctor`, nullary scalar inductive `ctor` and `default` | unsupported/heap alternatives |
| Primitive operations | `UInt8/16/32/64`, `USize`: 13 typed arithmetic/comparison/bitwise/shift/div/mod operations; `Float.add/sub/mul` on finite dyadics | all other runtime calls |

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

## Exhaustive pinned IR-constructor inventory and primitive registry

The exact-head native CI executes `scripts/VerifyIRInventory.lean` before
compiling the Rust backend. The Lean compiler itself enumerates constructors
of `IR.Decl`, `IRType`, `Arg`, `LitVal`, `Expr`, `Alt`, and `FnBody`.
It refuses any changed membership **or constructor order** relative to the
pinned Lean 4.34.1 ABI. The generated `artifacts/ir-coverage.tsv` records
each constructor as `conditional` or `refused`; `jdecl/jmp` are conditional
only for the typed scalar non-recursive join subset.

The backend now uses one `primitive-registry.tsv` for primitive codegen and
dependency classification. CI independently compares its set of 68 entries
with the Lean-generated coverage ledger. Unlisted operations and all
extern/IO/effect boundaries have no default adapter and must refuse. A real
`IO.println` fixture exercises this refusal through the public package API.

`conditional` is not synonymous with complete semantics. Arbitrary heap
objects, closures, full pattern matching, Nat/Int/Unicode collections,
floating-point conversions, mutation and reference counting remain
explicitly unsupported by this compiler version. This protects against
partial builds, but it does **not** complete checklist #193 items 16–19.

## Finite Float scalar arithmetic subset

For Lean IR `IRType.float`, the backend maps inputs, results and intermediates
to Rust `f64`. Only exact `Float.add`, `Float.sub` and `Float.mul`
primitives are permitted, lowered to Rust IEEE-754 `+`, `-` and `*`.
A real original-Lean oracle fixture compares generated functions on finite,
exact dyadic inputs including negatives and zeros.

This is **not** unrestricted floating-point semantics. NaN/signalling,
infinity/overflow, conversions, Float32, exception flags, unusual rounding
modes and other operations remain outside the verified domain and refuse.

## Nullary inductive / tagged-scalar subset

A Lean inductive constructor with **no object, usize or scalar fields**
can be lowered to its `IRType.tagged` constructor index, carried in Rust as
`usize`. Generated `FnBody.case` checks constructor identity against the
declared inductive type; branch-local values cannot leak across arms.
`Alt.default` is supported for this tagged-scalar case. Unknown tags trap,
rather than being silently interpreted as a different constructor.

The native suite independently evaluates 384 Rust checks from original Lean
source for a three-constructor nullary inductive. A separate field-carrying
inductive is refused and the previous output preserved. **This is not**
general constructor allocation, heap-backed pattern matching, closures,
captured variables, arrays or sharing semantics; those require a separately
specified object runtime and are still unsupported.

**Pinned compiler observation:** For the three-constructor fixture, Lean 4.34.1
actually uses `IRType.uint8` storage. The lowerer therefore also handles
nullary `UInt8`-backed inductives, using original constructor identities
to distinguish them from Bool. No generic `usize` coercion is performed;
the original IR storage type determines the Rust scalar type.

## Unsigned total arithmetic and shift semantics (Lean 4.34.1)

In addition to add/sub/mul and comparisons, the pinned primitive registry
now supports `div`, `mod`, `land`, `lor`, `xor`, `shiftLeft`
and `shiftRight` for each of `UInt8`, `UInt16`, `UInt32`,
`UInt64` and `USize`. The 65 fixed-width primitives plus three
finite `Float` primitives are explicitly represented in the production
registry and Lean-derived coverage inventory.

Correctness cannot be delegated to raw Rust operators at the boundaries:
Lean defines unsigned division by zero as **zero**, remainder by zero as
**the dividend**, and unsigned shift counts modulo the operand bit width.
We use Rust's `checked_div`/`checked_rem` with their exact fallback
values and `wrapping_shl`/`wrapping_shr` with explicit width reduction.
Each operand/result type must match exactly.

The `BitwiseFixture.lean` suite compiles 35 real Lean roots and replays
2,240 independently evaluated assertions against standalone generated Rust.
Vectors include zero divisors, zero/maximum operands, 1-, 8-, 16-, 32-,
64-, and 65-bit shift counts, plus seeded values. This is still not
general `Nat`/`Int`, signed bitwise, arbitrary-precision computation
or cross-platform `USize` verification. There is no formal compiler
semantic-preservation theorem.
