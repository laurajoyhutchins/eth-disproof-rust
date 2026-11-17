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

**Formal scope:** [IndependentAffineBoundary.lean](../../eth/proofs/IndependentAffineBoundary.lean) defines the actual two-bit finite sum and proves the compact two-or-zero formula for all Boolean b,c. It also proves preservation under weighted contexts and composition with a second interface. That is a particular universal mathematical theorem, **not** formal verification of the arbitrary-size Rust Gaussian-elimination algorithm.

For small interfaces, the optional polynomial lowering translates boundary parity equations into exact integer-polynomial indicators. These can enter the existing egg search and independent polynomial checker. The textual tree lowering may grow exponentially with the length of residual equations; the compact affine representation and evaluator avoid that expansion. This experiment therefore does **not** show a full-pipeline speedup from egg on the general affine input.

Limitations: input is an explicit parity-equation system, not an automatically recognized general CNF. The implementation has no independently verified global bit-operation or peak-memory bound and no source-to-Rust correspondence to the pinned ETH QueryStream algorithm. Compact affine elimination does not refute ETH.


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
