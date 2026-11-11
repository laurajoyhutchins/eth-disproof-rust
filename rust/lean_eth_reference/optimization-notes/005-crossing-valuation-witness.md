# Optimization experiment 005: certify crossing weights from actual geometry

> **Read experiment 006 before using these weights for pruning.** This note certifies one row's coefficient, not a whole mode variable. A mode is shared across all its contributing target rows; its safe weight is the minimum row weight. In dense packets the extra geometry-specific improvement can disappear entirely.

**Status:** isolated, locally tested mathematical witness. Not yet connected
to the manuscript's real packet traversal or recursive contraction.

**Pinned original:** [quantitative-contraction.tex](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex), blob `51ba54efc29f51bbc0426f848003030da484f354`, equations `tensor-mode-expansion`, `tensor-mode-budget`, and lemma `tapered-hermite`.

## Original method and avoidable work

For an active contraction call, the source takes `L=2^a`,
`S={-L,...,L-1}`, `alpha=2^(a+1)` and a nonzero Hermite point
`t in S`. Write `i=v2(t)`. A crossing packet's column tile is
`y=y0+2^(i+1)*j`, with row slot `x`, so `D=t-y0+x` satisfies
`v2(D)<=i` by the source crossing-group argument.

The crossing-mode coefficient of geometric exponent `b` contains

```text
A(T) = C(T)/(C'(0)*(T-y0+x))              v2(A(T)) >= a+1-i
B(T) = (2^(i+1)/(T-y0+x))^b             v2(B(T)) = b*(i+1-v2(D))
```

Here `T=t+alpha*z`; because `v2(alpha*z)>=a+1>i`, adding this
formal deformation does not change the denominator's valuation when
`D` is nonzero. Coefficientwise use of the valuation requires the
source's integral local-coordinate/ring assumptions.

The manuscript conservatively charges weight `b+1`, and experiment
003 used `a+1-i+b`. Its own geometric estimate permits the stronger,
**per-crossing bound**:

```text
w_geom = (a+1-i) + b*(i+1-v2(t-y0+x))
       >= a+1-i+b
       >= b+1.
```

A monomial with beta-weighted guaranteed valuation at least `p_t`
vanishes modulo `2^p_t` in this local calculation. No such pruning is
valid solely from guessed weights or from an unrelated target precision.

## What this commit executes

`src/valuation_witness.rs` verifies the numeric geometry (point range,
nonzero denominator, tile residue, `i<u<=a`, and `v2(D)<=i`) and
returns original, coarse and geometry-refined weights. It also computes
the original tapered Hermite precision:

```text
h = ceil(3M/u)
D_t = 2^(a-i)
p_t = p + 8*h*D_t + 8*M*(a+1).
```

`tests/valuation_witness.rs` exhaustively inspects small integer
crossings, tests a strict improvement, invalid inputs and overflow, and
checks `p_t` against its source expression.

For `a=4,u=3,t=4,x=0,y0=1,b=3`, the original/coarse/geometry
weights are **4/6/12**. With toy `M=16,p=32`, the real source
precision formula is **1184**, not 32. These values do **not** claim
that the manuscript's active-call packing conditions hold at this
small scale. The earlier 61,523,748-to-45 count was an illustrative
weight-budget experiment, not a measured source-call optimization.

## Evidence and remaining conditions

Locally restored Rust 1.99.1 passed four new witness tests, formatting,
strict Clippy and the saved reference snapshot's other tests.
**Exact combined GitHub branch head CI is still pending**, following

This module checks the *numeric consequence* of packet crossing; it
does not prove that a tuple `(x,y0,t)` actually came from a legal
crossing-group assignment or that coefficient extraction/canonical
precision lifting preserves the proposed pruning through all recursive
children. Next instrument real packet geometry, mode counts and
bit-width costs, then compare the two pruning policies on the same
admitted calls. Keep the original policy available as the oracle.
