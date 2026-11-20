# egg two-output contraction DAG experiment

This standalone Rust experiment is a deliberately small application of
[egg 0.9.5](https://docs.rs/egg/0.9.5/egg/), with ideas from
[TASO](https://theory.stanford.edu/~aiken/publications/papers/sosp19.pdf)
and [Tensat](https://proceedings.mlsys.org/paper_files/paper/2021/file/cc427d934a7f6c0663e5923f49eba531-Paper.pdf).
It is not part of the root ETH workspace or canonical Lean compiler.

```sh
cargo test --manifest-path experiments/egg-contraction-optimizer/Cargo.toml
cargo run --manifest-path experiments/egg-contraction-optimizer/Cargo.toml
```

## Model and evidence

Input is `(pair output1 output2)` with integer constants, variables,
`+`, and `*`. The Rust optimizer performs bounded equality saturation
over a handful of ring identities; a finite DAG extractor chooses one
representation per reachable e-class. Each operation is charged **once**
even if both outputs use it. Input is already structurally hash-consed.

The two reproducible cases have these expected DAG operation counts:

| Input | Original | Target |
| --- | ---: | ---: |
| `(pair (+ a (+ b c)) (+ (+ a b) d))` | 4 | 3 |
| `(pair (+ (* a b) (* a c)) (* a (+ b c)))` | 5 | 2 |

The first case shows sharing missed by independently minimizing each
output's expression-tree size: each output still needs two additions
but a single `(+ a b)` node can serve both. The second case uses
factorization to make the complete output shared.

Before accepting a strictly cheaper candidate, an *independent*
polynomial canonicalizer expands both outputs in **Z[variables]**
with sorted commutative monomials and arbitrary-precision coefficients.
It compares exact coefficients. Too many terms or multiplication
pairs causes an explicit refusal. A wrong candidate is never
accepted just because `egg` puts it in an equivalence class.

The search caps e-graph iterations, nodes, elapsed time and extraction
states. `complete` covers the **finite, single-representative-per-class
extraction search only**, not unrestricted e-graph saturation or all
possible equivalent circuits. Unfinished search preserves the verified
input incumbent; it does not assert optimality. The objective is number
of distinct `+` and `*` DAG nodes. Timings and the evaluator's
operand-byte counter are preliminary measurements/proxies, not a
realistic arbitrary-precision bit-complexity bound.

## What this does *not* establish

No SAT boundary function, sum over internal variables, modular
precision, nonlinear phase, Lean proof, ETH counting improvement, or
worst-case asymptotic result. Neither random input agreement nor
finite polynomial normalization substitutes for a kernel-checked
Lean-to-Rust correspondence theorem. The independent normalizer is
a restricted mathematical verification mechanism, **not** Lean itself.

Next experiment: encode a certified affine SAT region with an explicit
boundary, add sum/eliminate operators with checked scope conditions,
then test whether DAG sharing survives whole-pipeline measurement
against an unchanged exact #SAT oracle. Include coefficient bit widths,
peak live bytes and certificate-checking overhead.

Notebook: [Equality saturation and certified graph extraction](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/concepts/equality-saturation-and-extraction.md).


## Source-derived finite CNF boundary experiment

The `sat` module compiles **actual CNF clauses**, rather than handwritten
arithmetic polynomials, to a two-output boundary contraction. The local
compiler enumerates all internal Boolean assignments and leaves boundary
variables symbolic. This is exponential in the number of internal variables,
so it is **not a faster general #SAT constructor**.

The fixture uses internal variables `u,v`, boundary `b,c,d,e`, and two
regions distinguished by the last literal (`d` versus `e`). Each region
contains four CNF clauses: `(!u | !v)`, `(u | v | b)`,
`(u | !v | c)`, and `(!u | v | third)`. Its four internal states
contribute `b`, `c`, `third`, and zero, respectively. The generated
boundary polynomials are `b+(c+d)` and `(b+c)+e`.
The two regions agree at some boundary values and disagree at others;
agreement at a single boundary assignment would be unsound.

The oracle enumerates CNF truth assignments independently, without
using the arithmetic compiler or egg. It checks **all 16 boundary
assignments** and two signed weighted outer-context sums. This tests
the entire interface rather than one closed count.

The fixture targets a **4 to 3** unique-addition DAG reduction through
equality saturation and cross-output extraction. Across all 16 boundary
assignments, this is **64 to 48** arithmetic evaluations of the
already-constructed boundary functions. The CLI also prints a byte-work
*proxy*, not a true bit-operation or runtime speedup. The costs of CNF
compilation, search, checking and memory must all enter any end-to-end
claim.

Run the test and run commands above. Enumeration budgets and egg search
limits are explicit and cause refusals rather than partial truth tables.
Optimization equality is independently checked as an integer polynomial
identity, which is stronger than equality only on Boolean boundaries.
There is no Lean kernel certificate, no formalized compilation theorem,
and no integration with the original ETH recursion.


## Compact affine boundary elimination

The separate Rust module [affine.rs](src/affine.rs) now handles explicitly represented parity-equation regions, a genuine restricted class of #SAT instances. Unlike the earlier enumerating compiler, the affine constructor performs binary Gaussian elimination on a packed matrix over GF(2). For k internal bits and internal-column rank r, the retained interface consists of only residual boundary consistency equations and the exact multiplicity 2^(k-r). It evaluates to zero when any residual equation fails.

The constructor performs **no internal assignment enumeration**. Its matrix construction and row operations use polynomial work and memory in the explicit equation matrix dimensions, with an explicit storage refusal. The multiplicity is arbitrary precision. Its independent small-instance oracle enumerates Boolean solutions directly.

A two-row example with equations u XOR v = b and u XOR v = c produces one residual boundary condition b=c and multiplicity two. Independent composition of two such regions with shared boundary is tested on every boundary assignment. A separate 128-internal-variable fixture returns 2^127 solutions without enumerating any internal states. An attempted direct oracle at that size explicitly refuses.

**Formal scope:** [IndependentAffineBoundary.lean](../../eth/proofs/IndependentAffineBoundary.lean) proves the original two-bit finite sum and CNF/XOR encoding. [IndependentAffineRankNullity.lean](../../eth/proofs/IndependentAffineRankNullity.lean) now proves the **general, all-dimensions GF(2) fiber-count formula**, including every boundary target. [IndependentAffineRowOps.lean](../../eth/proofs/IndependentAffineRowOps.lean) proves that arbitrary finite row-swap/XOR transcripts preserve all equations. These are universal Lean theorems, **not** formal verification of the arbitrary-size Rust implementation.

For small interfaces, the optional polynomial lowering translates boundary parity equations into exact integer-polynomial indicators. These can enter the existing egg search and independent polynomial checker. The textual tree lowering may grow exponentially with the length of residual equations; the compact affine representation and evaluator avoid that expansion. This experiment therefore does **not** show a full-pipeline speedup from egg on the general affine input.

Limitations: input is explicit parity equations or strict canonical XOR3 CNF blocks, not arbitrary CNF. The implementation has no independently verified global bit-operation or peak-memory bound and no source-to-Rust correspondence to the pinned ETH QueryStream algorithm. Compact affine elimination does not refute ETH.


### Strict source-CNF-to-affine bridge

The affine module now includes a **narrow, fail-closed CNF recognizer**. Each
accepted three-variable XOR equation must appear as exactly the four
canonical three-literal clauses encoding even or odd parity, in the
expected order. Every four-clause block is checked against the generated
canonical encoding. Unknown, reordered, modified, or incomplete blocks
are refused rather than inferred to be XORs. Thus the original input
can be an actual CNF without the constructor enumerating its internal
assignments.

For u XOR v = b and u XOR v = c, the recognizer accepts eight clauses,
constructs the two-row affine matrix and reduces it to a boundary
equality plus multiplicity two. The small case is independently
checked against the direct Boolean-CNF enumerator on every boundary
context.

The [Lean source](../../eth/proofs/IndependentAffineBoundary.lean)
additionally proves that the exact canonical four-clause encoding is
equivalent to the corresponding XOR equation for every triple of
Boolean values, and proves the two-block count formula. These
theorems certify the **mathematical pattern**, while the Rust
recognizer implementation and the general row-reduction backend
still lack full formal refinement proofs.

This is not a general XOR recognition algorithm and will refuse
many logically equivalent CNF encodings. The strictness is intentional
until an independently checked more flexible recognizer exists.


## Independent certificate replay and verified mathematics

The packed-bit affine eliminator now emits a finite transcript of row swaps
and XOR operations, plus ordered pivot columns. The separately written
[affine_cert.rs](src/affine_cert.rs) checker reconstructs the original
system as dense Boolean vectors and replays every operation. The public
elimination method refuses a result unless the independent checker validates
all pivot columns, rank and free dimension, boundary ordering, residual
equations, row-operation indices and XOR count.

The **free-variable subtlety** matters: free internal columns may appear in
pivot rows. Only *residual* rows must contain no internal columns. An
initially overstrong checker rejected valid examples; its corrected
invariant has passed the regression suite.

- [Pinned Rust and Lean verification](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44362293013)
  passed **26 Rust tests** and three Lean proof modules, with standard axioms
  only and no sorryAx.
- The Rust tests include **200 deterministic affine systems** checked on
  every Boolean boundary against independent direct enumeration, and
  negative mutations of transcripts, residuals and source equations.
- The general Lean theorem proves that each nonempty GF(2) affine fiber
  is in bijection with the kernel, hence has size 2^(k-rank).
  A second general theorem proves all finite row-permutation/XOR
  transcripts preserve the full equation system.

**Remaining refinement gap:** The Rust producer, certificate representation
and independently implemented checker have not been formally refined into
the Lean definitions. This is proof-supported, independently tested
implementation evidence, not a verified implementation of arbitrary SAT
or an end-to-end ETH speedup.

Notebook: [Affine elimination and replayable certificates](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/affine-elimination-certificates.md).


## BitVec64 correspondence layer (November 18, 2026)

The new [IndependentAffinePackedRows.lean](../../eth/proofs/IndependentAffinePackedRows.lean)
models the packed coefficient storage as a finite collection of 64-bit
words, plus a separate Boolean right-hand side. It proves that every
packed word XOR and row swap decodes to the corresponding individual
Boolean-bit operation, with the same equality for arbitrary finite
operation transcripts. Flat column indices are interpreted by
word = index / 64 and bit = index % 64. This is universal over the
modeled finite word-row shapes, not just a test on one matrix.

The [pinned Lean acceptance workflow](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44371318470)
passed with standard axioms only and no sorryAx.

Rust regression tests compare actual u64 word operations and RHS parity
against independently mutated flat Boolean rows after every step of
128 deterministic 32-operation transcripts. Other tests target columns
63/64 and 127/128, empty dimensions, and invalid row indices. The
[30-test Rust CI](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44371459539)
passed alongside the Lean module.

**Remaining trust boundary:** The Lean theorem establishes correctness
of the 64-bit-word *model*. The Rust word operations agree with a distinct
Boolean implementation in tested cases. The native Rust checker has not
been formally refined into the Lean semantics, and compilation, raw
usize validity, certificate serialization, and memory/bit-cost bounds
are not proved. See the
[technical notebook](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/affine-elimination-certificates.md).


## Strict raw-value certificate admission

The public affine eliminate method now routes through a **versioned raw-value certificate**, decodes that raw witness, and runs the independent dense-Boolean replay checker before returning a boundary interface. The source producer's unchecked witness function remains available for adversarial experiments.

The [raw-value contract](src/affine_wire.rs) uses version 1; tag 0 is row swap, tag 1 is target-XOR-source, and row indices and pivot columns are unsigned 64-bit values. It refuses unknown versions/tags, aliases, out-of-range indices, invalid or unsorted pivot lists, and conversions to platform usize that cannot be represented. This is a **typed raw-value schema**, not a serialized byte format or parser.

Explicit [VerificationLimits](src/affine_cert.rs) set max_cells and max_steps, each defaulting to 8,000,000. Checked multiplication rejects overflow and budget excess before the dense matrix is allocated; the transcript length is checked before replay. These limits do not bound the entire process, producer, or externally allocated raw input.

The [Lean packed-row model](../../eth/proofs/IndependentAffinePackedRows.lean) now has 8-bit raw tags, 64-bit raw indices, a checked finite-index decoder, a version-and-budget admission predicate, and a replay theorem. The formal lemmas prove that its decoder rejects unknown, aliased and out-of-range operations, rejects exceeded budgets, and preserves exact Boolean replay for accepted transcripts. This is a kernel-checked mathematical model, **not** a Lean refinement of the compiled Rust decoder.

The Rust suite additionally compares **720 tag/index cases** (5 row counts × 4 tags × 6 first indices × 6 second indices) and **3,900 pivot/dimension cases** to independently constructed acceptance predicates. The full path, corruptions, empty matrices and budget limits are also tested. See the [experiment workflow](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/workflows/egg-contraction-experiment.yml) for exact-head CI evidence.

Remaining open: formal correspondence of the entire native Rust verifier and terminal pivot/residual decisions to Lean, any canonical byte-serialization/parser proof, compiler and memory/ownership semantics, and a certified whole-pipeline cost bound.


## Terminal pivot/free completion theorem and witness

The [new Lean terminal theorem](../../eth/proofs/IndependentAffineTerminal.lean) proves, for **any finite pivot, free, boundary and residual index sets**, that a matrix with isolated pivot variables and boundary-only residual constraints has exactly **2^number_of_free_variables** internal solutions for a feasible boundary, or zero otherwise. Free columns may remain in pivot equations. An additional theorem transports the result through *any bijection* between the actual internal-column order and the pivot/free partition; pivots need not be consecutive.

The independent [Rust checker](src/affine_cert.rs) now constructs a read-only **VerifiedTerminal** from independently replayed source rows, only after all earlier pivot isolation, rank, boundary-order, and residual-equality checks succeed. Its **complete** method calculates the unique pivot extension from free and boundary bits, returning None for impossible residual contexts. Its **count_at** method implements the resulting exact count. Witness fields are private to prevent accidental unchecked construction.

The Rust suite checks every boundary for **200 seeded small affine systems**, enumerates every free assignment, verifies every completed internal assignment against the original equations, and confirms no duplicate completions. A noncontiguous-pivot fixture has pivot columns 1 and 4 and free columns 0, 2, 3 and 5, with exactly 16 completions in feasible contexts.

[Exact-head experiment CI](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44614539579) passed **38 Rust tests** and the pinned Lean 4.34.1 theorem check. [Original ETH Rust CI](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44614539583) passed at the same commit.

**Formal boundary:** The terminal counting theorem is kernel-verified and applies to the *mathematically specified* normal form. The executable checker and terminal witness are independently tested, **not formally refined to Lean**. This does not prove the compiled Rust program correct or establish general #SAT/ETH complexity.


## Checked full-row terminal shape and source occurrence parity

The [new Lean terminal check theorem](../../eth/proofs/IndependentAffineTerminal.lean) applies to the **full replayed equations**. Its accepted block structure requires an identity pivot-by-pivot matrix and zero residual-internal blocks, while permitting unrestricted free-variable coefficients in pivot equations. It proves the full system has exactly 2^(free dimension) internal solutions at feasible boundary assignments, and none otherwise. The earlier arbitrary-column theorem handles noncontiguous pivots.

[IndependentAffineSourceRows.lean](../../eth/proofs/IndependentAffineSourceRows.lean) verifies source-list-to-GF(2) row reconstruction for arbitrary finite variable sets and occurrence lists, including duplicate-name cancellation, and relates Boolean XOR folds to the reconstructed coefficient row.

The Rust independent checker suite now includes falsification cases for missing or unisolated pivots, internal bits in residual rows, and changed boundary residuals. It also accepts the legitimate free-variable coefficients in pivot equations. [Pinned exact-head CI](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44638863761) passed **six Lean modules and 39 Rust tests** with no sorryAx, and the [original ETH Rust CI](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44638863755) passed at the same commit.

**Trust boundary:** The new Lean theorem validates the mathematical predicate for a replayed terminal matrix; source occurrence parity is likewise a mathematical theorem. The actual Rust string lookup, row assembly, terminal checker decisions and machine-level resources still lack a source-to-Lean implementation refinement proof. No general SAT or ETH speedup is claimed.


## Independent Lean audit of native Rust-produced certificates

The opt-in Rust CLI emits **data-only Lean fixture records**, not claims trusted by the Lean side:

~~~sh
cargo run --manifest-path experiments/egg-contraction-optimizer/Cargo.toml -- --emit-lean-certificates
~~~

The [Rust emitter](src/affine_native_lean.rs) serializes original source equation occurrence lists, raw row operations, pivot columns and the claimed boundary interface into closed Lean terms. Names are decimal UTF-8 byte lists, not executable text. It emits six valid receipts from the live producer and six fault-injected negative receipts.

The [independent Lean auditor](../../eth/proofs/IndependentAffineNativeAudit.lean) reconstructs coefficient rows **from source occurrences**, replays raw swaps and XORs and checks the terminal certificate independently of the native checker. Lean proves closed receipt acceptance/refusal equalities using the kernel-checked decide tactic. Five small accepted cases are also exhaustively checked against direct Boolean source counting, for **every boundary assignment**. A 130-variable case crosses packed-word boundaries but does not use exponential direct counting.

The pinned [exact-head CI run #44743370753](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44743370753) passed the generated Lean audit, seven Lean source modules and **40 Rust tests**. The [original ETH Rust CI #44743370842](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44743370842) independently passed at the same commit.

**Trust boundary:** This is a finite, actual-Rust-output cross-implementation test with kernel-checked Lean propositions, not a universal formal refinement of the Rust source, compiler or binary. The fixed Lean auditor and limited fixture emitter are not an arbitrary byte protocol parser. The Rust data structures, every input/rejection path, machine memory semantics and worst-case costs remain separately unverified.

Notebook: [Affine elimination certificates](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/affine-elimination-certificates.md).


## Source-name admission and indexed row construction

The producer formerly enforced `[A-Za-z][A-Za-z0-9_]*`, while the independent Rust checker accepted some other nonempty names. This was a supported-input domain mismatch, not an algebraic counterexample. Producer and checker now use the same explicit Rust identifier validator; the separate Lean receipt auditor independently implements the grammar on UTF-8 byte lists.

The regression test renames a **declared variable and all its equation occurrences together**. Although the mathematical affine system remains identical, malformed source names must be refused. The Rust-to-Lean emitted corpus includes leading-digit, hyphenated and non-ASCII negative controls.

[IndependentAffineIndexToggle.lean](../../eth/proofs/IndependentAffineIndexToggle.lean) proves a universal correspondence for the specified row-construction algorithm: given distinct registered names and a lookup returning the registered column for each source occurrence, performing all indexed Boolean toggles produces exactly the source-occurrence parity coefficients, for any finite number of variables and occurrence-list length. Duplicate occurrences cancel. This is a **theorem with explicit lookup-correctness assumptions**, not a formal proof of the Rust `BTreeMap`, `Vec`, allocator or binary.

[Pinned experiment CI #44745997859](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44745997859) passed the new Lean theorem without `sorryAx`, the Rust-to-Lean corpus and **41 Rust tests**. The [original ETH Rust workflow #44745997807](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44745997807) also passed at the same code commit.

Remaining implementation gap: demonstrate that native map insertion/lookup and bit-vector indexing actually refine the specified lookup/update operations across all supported inputs, followed by the rest of the independent Rust checker. See [the notebook derivation](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/affine-elimination-certificates.md).


## Checked source-name lookup at the mutation boundary

The independent Rust checker now retains the original ordered declarations beside the BTreeMap index. The map only supplies a **candidate** column: every lookup checks that the original name at that index equals the requested name, and every bit update uses bounds-checked mutable access. Wrong-but-in-range indices, missing entries, RHS-pointing indices and short rows are refused before mutation.

The universal [Lean checked-index theorem](../../eth/proofs/IndependentAffineIndexToggle.lean) proves that **every accepted raw name/index transcript** has the same coefficient bits as parity over its source variable occurrences, for pairwise-distinct registered names. It no longer assumes the candidate map index is correct, because checking the original ordered names discharges that property on success. This is a mathematical proof of the **checked algorithm**, not of Rust BTreeMap or Vec internals.

Native tests corrupt the registry with wrong in-range and out-of-range indices, RHS indices and missing entries; none may mutate the row. Another test compares 128 seeded 128-occurrence sequences to direct source-name parity after every toggle. The [pinned CI run](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44748607741) passed the Lean source-parity theorem, the Rust-to-Lean receipt audit and **43 Rust tests**; [Lean proof style](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44748607611) and [original ETH Rust CI](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44748607721) also passed.

**Still open:** Source- or compiler-level proof of the actual Rust lookup, bounds-checked indexing, memory operations and complete verifier control flow, as well as runtime resource and generic SAT/ETH complexity claims. The [notebook study](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/affine-elimination-certificates.md) explains the proof obligations and negative findings.


## Bounded machine-level verification of the actual Rust slice update

The independent affine checker validates the proposed column against the original ordered source names and then calls the **real** [checked_toggle.rs](src/checked_toggle.rs) Rust primitive. That module performs `row.get_mut(proposed)` followed by one Boolean flip, or refuses without writing. It is compiled into the running verifier, not copied into a test-only implementation.

The separate [Kani workflow](../../.github/workflows/affine-checked-toggle-kani.yml) directly checks the same Rust file with **Kani 0.68.0**:

```sh
# From experiments/egg-contraction-optimizer, after installing Kani 0.68.0:
kani src/checked_toggle.rs
```

The harnesses analyze a four-bit row with symbolic initial bits and every `u8` candidate index, plus truncated and empty rows. They assert exact single-bit framing for successful access and atomic refusal for absent positions. [Workflow #44754372798](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44754372798) passed both harnesses: **0/41** and **0/66** failed checks (one unreachable check in the latter).

**Scope and negative result:** This is a bounded source-level machine check, **not** a proof of arbitrary `usize` inputs, source-name equality, `BTreeMap`, or the full compiled verifier. The initial [whole-crate Kani run #44751435855](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44751435855) verified the short-row harness but spent its remaining 15-minute limit unwinding `memcmp` in a symbolic string-comparison harness. Splitting the concrete mutation primitive from name admission eliminated that solver obstacle. The universal checked name/index semantics remain separately kernel-checked in [IndependentAffineIndexToggle.lean](../../eth/proofs/IndependentAffineIndexToggle.lean).

See the [technical notebook study](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/affine-rust-slice-model-checking.md) for the precise proof and trust boundaries.
