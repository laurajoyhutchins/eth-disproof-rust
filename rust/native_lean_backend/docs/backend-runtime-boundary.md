# Rust backend ↔ Lean runtime contract

**Status:** design and acceptance contract; not yet an implemented
`lean-c` code-generation mode. Pinned source: Lean 4.34.1, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`.

## Boundary

The source of truth is the executable `Lean.IR.Decl` after Lean's compiler
has performed allocation/reuse/ownership lowering. The one Rust Reader should
emit operations with **source ownership effects**, not construct a new
reference-count schedule. The first runtime behind generated Rust must be
the official Lean runtime. After this backend works, a Rust-native runtime
can implement the same operation-level interface.

```text
                      Lean.IR.Decl
                            |
                    one Rust Reader
                            |
                    generated Rust
                            |
                  owned/borrowed ABI
                     /          \
          official Lean C        future Rust-native
              runtime                runtime
                 |                      |
             reference                comparison
```

The existing Lean IR decoding shim is an implementation detail for reading
the borrowed `Lean.IR.Decl` inside the compiler. The execution-runtime
shim is a **different boundary** and should not expose unchecked compiler
heap objects or create Rust-owned copies of source IR.

## Required runtime operations

`lean.h` has header-inline operations: generated Rust cannot always link
directly to them by name. Bind them through a small C translation unit
compiled and linked against the **exact pinned header and runtime**.
Do not fabricate ABI prototypes or use layout guesses.

| Source IR / effect | Initial runtime behavior |
| --- | --- |
| `ctor` / `proj` / `uproj` / `sproj` | Allocate original Lean object and read original pointer/scalar fields with the correct offsets |
| `inc`, `dec`, `del` | Perform the **exact source instruction's** reference changes or shell deletion, with its checked/persistent/count variants |
| Borrowed formal or projection | A non-owning view whose lifetime is protected by a live source reference, not a Rust `Rc` clone |
| Owned formal / return / move | Transfer one existing source-owned reference without implicit Rust Drop or clone effects |
| `isShared` | Observe official Lean runtime sharedness at the exact source instruction |
| `reset`, `reuse`, `set`, `setTag`, `uset`, `sset` | Enforce original uniqueness, field layout, alias and reuse semantics; no copy-on-write approximation |
| `fap`, `pap`, `ap`, `jmp`, `case` | Preserve source call/return ownership, closure captures and branch/join control flow |
| `extern`, exceptions, IO | Bind reviewed Lean runtime implementation or explicitly refuse; never replace with an unrelated host callback |

Important C semantics from pinned `lean.h`:

- `lean_inc` and `lean_dec` skip tagged scalars, and adjust heap reference
  counts for objects.
- `lean_is_shared` reads source-runtime reference-count state.
- `lean_ctor_set` overwrites a constructor pointer field without
  automatically decrementing the replaced value. It cannot be replaced
  by a generic Rust collection assignment with different destruction.
- `lean_dec_ref` may destroy a last-reference object; projecting a child
  without owning the child does **not** keep the child alive.
- Object allocation and field access are not equivalent to cloning a
  standalone `Rc`-backed immutable object.

This contract is deliberately about the *physical* instructions, even when
a pure result would be identical after changing reference counts.

## Rust representation

Use one opaque pointer/handle representation at the FFI boundary.
Represent **borrowed** and **owned** source references distinctly in
generated Rust. Do not implement an implicit `Drop` or `Clone` that changes
Lean reference counts on a compiler temporary's lifetime.

An explicit source `inc` is the sole authority for increasing a source
reference; `dec` and `del` must distinguish decrement-and-release from
deleting a constructor shell and transferring its fields. A moved owned
reference must not be released again. Type and effect verification belongs
before emission; the only `unsafe` execution surface should be audited
runtime wrappers and generated call edges.

## First backend slice: exact ownership effects

Build one fixture from **unchanged Lean source**, captured after the pinned
Lean compiler emits final IR. Require the selected executable closure to
actually contain and exercise:

1. `ctor` and a borrowed `proj` (parent retains the child's protection).
2. An explicit `inc` preserving a projected field across parent release.
3. An explicit `dec` or `del` that can invalidate an unretained
   projection. The rejected case must refuse rather than becoming
   artificially safe because Rust still holds an `Rc`.
4. `isShared` before/after increment, plus at least one function boundary
   with a borrowed formal and one with an owned transfer.
5. An independent Lean C executable from the **same** original source
   producing value and object/RC-event traces on the same inputs.

Do not hand-write Rust that resembles the source and call it compiler
acceptance. The artifact must be emitted by the single production Reader,
using only an admitted IR grammar. A missing operation is a precise,
source-derived refusal.

The first step is **B0: emit a supported scalar declaration using the Lean C
runtime provider** without perturbing existing generated-Rust output. B1
then admits the ownership fixture above. The order keeps a minimal
code-generation/linking smoke before a difficult physical-object proof.

## Gate definitions

- **B0 (backend wiring):** generated Rust links and executes on original
  Lean runtime; pinned runtime identity and ABI recorded, no independent
  Rust runtime semantic assumptions.
- **B1 (ownership):** source and generated Rust follow equivalent
  branch, ownership, sharedness, allocation and release traces on named
  fixtures; unsupported patterns refuse.
- **B2 (control flow):** calls, joins, closures, recursion, mutation and
  imported transitive closures match independently executed Lean C.
- **B3 (general release):** three substantial, unchanged external Lean
  projects, source/module provenance, exact-head CI, fail-closed refusals,
  and performance measurements.
- **R1 (runtime replacement):** Rust-native implements the **same** runtime
  API and passes all B0–B3 semantic and physical checks independently.
  Optimizations require a specified observational refinement relation.

Report functional equivalence, physical trace evidence, total allocations,
peak live bytes, peak RSS, and latency separately. **Finite differential
agreement is not a general theorem of generated Rust semantics.**

## Non-goals

- Rewriting Lean's parser, elaborator, optimizer, or language.
- Generating code directly from an independent LCNF representation.
- Implementing a second Rust ownership optimizer.
- Replacing the Lean proof kernel in this compiler project.
- Claiming to extract executable code from noncomputable ETH definitions.
