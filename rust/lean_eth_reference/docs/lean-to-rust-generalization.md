# Compiling the original Lean ETH program to Rust without flattening it

Status (2026-11-12): **verified source-graph compiler vertical slice**, not an end-to-end ETH counting port.
The complete original QueryStream program is not executable in Rust; the finite Lean
kernel certificates do not constitute a universal proof of native Rust runtime
correctness. The native JSON graph loader is the **only** source-graph execution
path; Python is retained for Lean export orchestration, test generation, and
independent acceptance evidence, not for emitting `Block` constructors.

## Scope and preservation contract

The original source of truth is `openai/math@4eaee87548250b2682affda7d05d947c05554bae`
with Lean 4.34.1 and the pinned Mathlib dependency. The goal is the *complete
executable source closure* of the ETH SAT implementation, including
`SqrtLogSpace.QueryStreamProgram.program` and the native counting path,
not textual translation of every theorem in the imported mathematical library.

A Lean `theorem`, proof of `Prop`, quotient/law, or noncomputable
mathematical specification does not become a Rust function merely because
it appears in the import graph. Lean keeps checking those definitions and
their proofs; the export boundary contains only well-founded executable
data and functions. Any purported executable dependency on a genuinely
noncomputable term must be explained or refused, never replaced with a
numerical oracle or a guessed value.

Do not claim an ETH disproof, polynomial complexity, or Lean/Rust
equivalence from successful Rust compilation.

## Finding in the original source

`StructuredProgram.Cmd` contains atoms, sequencing, if-then-else, and
while. `StructuredCalls.Cmd` adds calls to finite `BitProgram.Program`s.
`ProgramLinking` provides physical relocation, lifting and linking of
register/stack/label maps. These are reusable *source definitions* with
existing Lean execution-preservation theorems.

The legacy generator traverses `Fin l` for every label of each
`Program r s l` and repeatedly invokes `Meta.whnf` to extract a
`BitProgram.Instr`. It is exact when it finishes, but the work and
intermediate memory grow with the fully expanded table size. One source
declaration, `SqrtLog.Setup.computeLProgram`, refused at two million
Lean heartbeats in the seven-target batch. Repeatedly raising heartbeats
is not a generalized solution.

The new Rust `DeferredProgram` is a provisional *consumer* for a
source-grounded graph. It preserves label 0 as the original source halt,
calls as their full source physical label spaces, and allocates one
shared node per constructed operation instead of one instruction per
label. Its synthetic repeated-subgraph test represents 268,435,456
physical sites in a small shared DAG, without materializing a table.
This is a test of the representation, **not** a measurement of original
ETH source size or mathematical complexity.

## Required intermediate representation

The transport format should be a versioned, deterministic, source-bound,
typed declaration graph. A `Program` node carries the exact original
declaration, source blob, dependencies, finite register/stack dimensions,
entry, input/output ports, and control root. An instruction retains all
12 original source constructors; no #SAT semantic shortcuts.

The next graph node forms, in implementation order:

| Node | Meaning | Physical source obligation |
| --- | --- | --- |
| `Atom`, `Skip` | `StructuredProgram` leaves | Exact source instruction |
| `Seq`, `Branch`, `While` | Structured composition | Exact `siteEquiv` order and continuation |
| `Call`, `Reference` | Shared callee | Original label count, entry, halt-to-return relocation |
| `Table` | Already source-verified finite instruction table | Byte-identical instructions and validated Fin indexes |
| `Lift` | Register/stack embedding | Injective source-port map, unchanged physical labels |
| `Link` | `ProgramLinking.linkInto` / `link` | Left halt becomes jump to right entry; exact offsets |
| `Repeat`, `Fold` | Proven fixed combinator generators | Same order/size/entry as Lean recursion, without expansion |
| `CodeAt` | Residual pure `Fin l → Instr` term | Must yield exact physical instruction or typed refusal |

The source-elaborated Lean graph producer exports bounded, source-bound
`original-structured-source-v1` command roots and
`original-linked-source-v1` physical-program roots. The latter preserves a
direct `ProgramLinking.liftProgram`, `link` or `linkInto` without inserting
an artificial call site. Both use the same native Rust source-graph decoder.
This new root protocol has synthetic physical-layout and refusal tests; pinned
original-Lean source-root acceptance remains a separate verification gate. The native Rust loader validates the
complete schema, source identifiers, expected certified SHA-256, finite
operand/port/label bounds, and lowered physical sites; immutable equal callees
are interned by full ABI and instructions. `Atom`, `Skip`, `Seq`, `If`,
`While`, and finite `Call` are accepted. `Repeat` is a validated source-graph node for the restricted elaborated
`Nat.rec skip (fun _ acc => seq acc fixed) count` command form (including
its mirrored sequence orientation). The Rust source decoder and independent
Python physical oracle preserve exact per-site continuations without flattening.
Neither arbitrary `Nat.rec`, parameter-dependent folds, nor `List.foldl`
may be silently translated as fixed repetition.
`Lift` and `Link` (including heterogeneous `link_into`) are now decoded into
bounded on-demand physical source views by the **same native Rust loader**.
The loader checks the exact source SHA-256 binding, typed port dimensions,
injective maps, source opcode bounds, and caller relocation. `Fold` and
unbounded integer addresses remain unsupported and refuse.

### Physical layout matters

Original Lean `StructuredCalls.compiled` reserves physical label **0**
for halt, and places every command site at a positive physical label.
An embedded callee's halt changes into a jump to its caller continuation.
Branch and while control sites also count as physical steps. These facts
must hold under any symbolic representation; skipping a call/branch as a
host-language operation changes the source trace and cost model.

The preexisting eager Rust `Cmd::compiled` uses a different halt-label
layout in some branches. Compare complete source physical labels, not just
terminal register values. PR #156 contains independent exact original
Lean full-state differential evidence for a separate compiler repair;
reconcile it before the generalized generated source is accepted.

Do not conflate source BitProgram steps with the primitive TM2 overhead or
machine bit-complexity. Keep separate measurements and explicit maps.

## Reproducible original-source acceptance

The `Original Lean source-graph physical parity` GitHub workflow has two
explicit suites, selected with **Run workflow** (`workflow_dispatch`), not
by a transient branch name:

- `original` (default, and the suite for compiler PRs): six pinned original
  Lean program exports, independent physical transition differential, kernel
  certificates, generated Rust tests, and the structural `computeL` probe.
- `fixtures`: source-derived original-Lean `lift`, `link`, `linkInto`,
  and fixed `Nat.rec` repetition; each is independently exported as a physical
  Lean table, checked by the Lean kernel, and compared with generated Rust.
  The optional `fixture_names` input selects a space-separated subset
  (for example `repeatedRoot`); empty runs the entire fixture suite.

Both suites pin the original `openai/math` commit, Lean and Mathlib. Passing
either suite is evidence for its selected source programs, **not** a universal
Rust runtime refinement theorem. Unknown fixture names refuse rather than
silently running a different suite.

## Verified acceptance boundary

The original pinned Lean source and Lean 4.34.1/Mathlib were independently
used to verify six finite source-derived graphs, spanning **143 exact physical
labels**, with machine-checked equal entry, ports, all instructions and
one-step transitions for arbitrary source configurations. Independent
Lean/Rust physical tests matched **8,989 bounded complete-state transitions**.
The original `SqrtLog.Setup.computeLProgram` (212 labels, 37 graph nodes)
was exported structurally and executed in Rust for bounded inputs, without
an independently proved full physical table. See GitHub Actions
`original-source-graph` workflow for live, exact-head receipts, not
unversioned status assertions.

A matching JSON SHA-256 is **not** an authorization by itself: callers must
bind the digest to an independently checked Lean kernel certificate. Rust's
decoder and physical executor remain supported by finite differential tests,
not a universal machine-checked correspondence.

## Lean producer

Implement an original-Lean `MetaM` exporter run under the pinned Lake
environment. It must not reimplement the Lean parser in Python or Rust.

1. Load only the transitive executable entrypoint closure by original
   declaration identity, with the exact original Git and Mathlib pins.
2. Inspect the elaborated, fully typed declaration value. Reduce only
   enough of its **outer constructor** to recognize
   `StructuredCalls.compiled`, `StructuredProgram.compiled`,
   `ProgramLinking.liftProgram` / `linkInto`, concrete
   `BitProgram.Program` records, and their structured `Cmd` variants.
   Do not normalize every `p.code i` to discover a program's shape.
3. Retain references to subprogram constants and parameter substitutions.
   Memoize by elaborated declaration, arguments, source identity and
   type. No textual guessing from an unelaborated name.
4. Reflect finite port maps under bounds with a closed, typed representation;
   require injectivity where the source theorem assumes it. A failed map
   is not silently substituted with identity.
5. Recognize original fixed combinator generators (`Nat.rec`,
   `List.foldl`, `Fin` cases, static repetition) as
   `Repeat` / `Fold` or residual pure `CodeAt` nodes when preserving
   exact semantics is possible. Fall back to per-label
   `Meta.whnf` **only for a bounded leaf**, not the entire program.
6. Detect cycles and partial reductions. Record the smallest unsupported
   declaration/path and a machine-readable reason. Put no synthetic
   "successful" table in its place.
7. Emit canonical graph bytes, graph node counts, source file Git blobs,
   transitive declaration identities, source/Lean/Mathlib pins and a
   SHA-256 receipt. The Rust consumer checks them all before codegen.
8. Preserve independent original Lean trace producers. Generated Rust
   must never be used as its own Lean oracle.

The consumer must not execute arbitrary Lean code or an untrusted JSON
expression. It accepts a fixed schema of typed instruction/graph nodes and
refuses unknown node tags, oversized payloads, cycles, non-injective
required maps, integer overflow and out-of-range finite indexes.

## Large address spaces

`BitProgram.Program` uses mathematical `Nat` and `Fin` label counts.
A `usize` Rust program counter is sufficient only if every source
address fits it. The graph IR must eventually represent symbolic control
paths or an exact unbounded integer index, with a proven mapping to the
Lean numeric label. Do not truncate large source sizes into machine words
or claim execution coverage after a conversion refusal.

A graph can be compact while its execution still takes exponentially
many source steps. Shared DAG storage does **not** establish a
nonexponential algorithm.

## Verification ladder

These are distinct gates and must be reported separately:

1. **Source-bound:** original typed declaration, upstream Git blob,
   dependency closure and toolchain verified.
2. **IR validity:** closed supported graph, typed dimensions and port maps,
   complete source instruction forms, no unsupported fallbacks.
3. **Compilation:** Rust graph consumer builds and executes the supported
   graph; a small optional full materialization matches exactly.
4. **Physical differential:** for each supported original node kind,
   independently execute the pinned *original Lean* one-step semantics and
   Rust's deferred engine on exactly matched initial states, checking
   every PC, register, stack, halt, capacity refusal and step count.
5. **Compositional refinement:** a Lean theorem, or explicit residual
   obligation, connects each graph constructor to original
   `StructuredCalls.code` / `ProgramLinking.relocateInstr` semantics.
6. **End-to-end:** the complete source-defined SAT frontend, counting
   control, output ABI and adversarial bounded inputs run without a
   host-side oracle substitution.
7. **Cost:** source physical steps, primitive TM2 overhead, peak stack
   bits, Rust heap bytes and measured bit operations are separately
   recorded. No complexity result without a proved worst-case bound.

For a counterexample, save both independent producer inputs and traces
with immutable source and generated hashes. Reproducible refusal is a
correct outcome; a forged or cached matched trace is not.

## Practical sequence

A. Land the deferred Rust graph executor and its table/eager differential
fixtures (PR #167). It is a backend prototype, not a source exporter.

B. Extend the IR with source-pinned lift/link and shared call edges; then
measure bounded exact original source nodes, including the six
independently exported composed programs in PR #161.

C. Export the same six programs as *structured IR*, verify their complete
physical instruction tables against the already accepted source tables,
and then verify independently executed original Lean state traces. This
is the key cross-implementation acceptance gate.

D. Handle `computeLProgram` as the first nontrivial generator case,
without increasing global heartbeat limits. Add bounded folds/repeats
or residual code-at semantics only when exact label equivalence is tested.

E. Expand across the `QueryStreamProgram` *executable* dependency DAG,
recording coverage per unique declaration and per graph kind. Keep
denominator/factor and counting semantics explicit. Reuse existing native
Rust implementations only after exact correspondence is demonstrated.

F. Generate native Rust modules from the verified IR once graph execution
is established. Specialized native kernels require their own equivalence
and performance evidence; otherwise use the correct generic interpreter.

An optional native Lean C backend + Rust FFI may provide execution of
unsupported *computable* Lean definitions with the Lean runtime, but it
is not a Rust-native port and cannot certify source-level BitProgram
step parity on its own. Use it as an explicitly labeled interoperability
fallback, not as a way to inflate translated-source coverage.

## Definition of done

Every executable declaration reachable from the target original ETH
entrypoints is classified **native-from-IR**, **verified fallback**, or
**unsupported with a precise reason**. A fully native port requires the
last category to be empty in that closure, physical and semantic
differential gates to pass, and the true end-to-end computation to run.
Theorem declarations remain Lean-checked, not blindly translated.

### Native ProgramLinking source integration (PR #175)

The single native Rust `DeferredProgram::from_original_source_json` loader
now recognizes original `ProgramLinking.liftProgram`, `link`, and
`linkInto` nodes, including different left/right finite dimensions. It
resolves physical instructions *on demand*, using the existing native
port-relocation and label-shift operations. It does not construct or execute
Python-generated Rust blocks. The Python graph parser remains an independent
structural verifier and Lean-table comparator, **not a Rust compiler**.

The serialized graph is SHA-256 and declaration bound. Its total byte and
node budgets remain strict, and individual finite tables are capped at 4,096
labels. The native executor's 1,000,000,000-label **symbolic address cap** is
not permission to materialize a large table or an assertion of resource
feasibility. Unsupported constructors, ill-typed or non-injective mappings,
and overflow refuse explicitly. Original Lean kernel certification of each
specific exported graph remains a separate requirement.

The first exact-source and native acceptance [passed at an earlier restacked
head](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43325069177).
Final-head source acceptance and the complete original query/DFS/counting
execution must pass independently before the entire Lean-to-Rust port can be
called verified.
