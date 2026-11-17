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
