# Optimization experiment 006: a mode's valuation belongs to every row

> **Source-structure correction (experiment 007):** In a genuine source packet, every real column shares its slot with a real row. For any nonempty tile, a paired target row forces the mode-wide geometric weight to **equal** the uniform coarse bound `a+1-i+b`. Thus the sparse single-row improvement hypothesized below cannot arise for a nonzero source mode. See [007](007-paired-packet-occupancy.md). The conditional row-arithmetic identities and their counterexamples remain valid, but are not evidence of an implementable extra speedup.

**Status:** executable *conditional* whole-mode certificate, tested against the
unchanged original finite Rust port and an independent small integer
calculation. No live packet-to-mode integration or end-to-end speedup claimed.

**Pinned source:** [quantitative-contraction.tex](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex)
(blob `51ba54efc29f51bbc0426f848003030da484f354`), at
`eq:tensor-mode-expansion`, `eq:tensor-mode-budget` and the paragraph
introducing one mode variable **per packet, tile and b**, subsequently used
in multiple row factors.

## The defect in the previous optimization proposal

Experiment 005 proves a valuation lower bound for **one row** with
denominator `d_x=t-y0+x`. But the manuscript's mode `Z` is shared
between all crossing rows `x` in that packet and tile. The coefficient
of `Z` in each row form can have a different 2-adic valuation.
Pruning a global exponent `beta_Z` using a selected high-valuation row
would silently omit terms of lower valuation contributed by other rows.

This is not a defect in the original algorithm: its weight `b+1` is
uniform and therefore safe.

## Source-derived correction and an additional exact identity

Write `i=v2(t)<u`, `L=2^a`, `alpha=2^(a+1)`, and
`v_x=v2(t-y0+x)<=i`. The crossing coefficient is

```text
A_x(z) =
  C(t+alpha*z) / (C'(0)*(t+alpha*z-y0+x))
    * (2^(i+1)/(t+alpha*z-y0+x))^b .
```

Because `C(t)=0` and the source's complete residue grid gives
`v2(C'(t))=v2(C'(0))`, its **linear coefficient** satisfies

```text
[z] A_x(z) = alpha*C'(t)*2^((i+1)*b)
                  / (C'(0)*(t-y0+x)^(b+1))

v2([z] A_x) = (a+1-v_x) + b*(i+1-v_x).
```

The source integrality/crossing argument also establishes that **every
higher coefficient** is divisible by at least this power of two, so it
is a coefficientwise lower bound, not merely a linear-term observation.

For the *complete contributing row set* `R_Z`, the safe mode bound is

```text
w_Z = min_(x in R_Z) [(a+1-v_x)+b*(i+1-v_x)].
```

A product of mode coefficients has valuation at least
`sum_Z beta_Z*w_Z`; a tuple with that sum >= the **actual source**
`p_t` can be omitted modulo `2^p_t`. This claim remains conditional
on the caller supplying all real contributing target rows and a source-
legal packet/group assignment. The Rust API deliberately names that
assumption; numeric geometry alone cannot establish completeness.

## What the tests found

For `a=4,u=3,t=4,y0=1,b=3`:

| Row support | Original b+1 | Experiment 003 | Experiment 005 row-bound minimum | Corrected mode bound |
| --- | ---: | ---: | ---: | ---: |
| x=0 only | 4 | 6 | 12 | 14 |
| x=0 and x=1 | 4 | 6 | 6 | 6 |

The second row has `v2(t-y0+x)=v2(4)=2`, so using the first
row's weight 14 for the complete mode would be incorrect.

An even more general negative finding: if the real target row
`x=y0` is present, then `v_x=v2(t)=i`. Consequently the
geometry-refined whole-mode weight equals the *coarse* bound `a+1-i+b`.
A fully occupied packet therefore cannot benefit from extra
row-specific geometry refinement at this tile. Any additional benefit
requires missing rows or other certified support restrictions.

At the **source precision formula** `p_t=1184` for the *illustrative*
`a=4,u=3,M=16,p=32,i=2`, counting two modes `b=0,3` gives:

| Policy | Weights | Candidate tuples |
| --- | --- | ---: |
| Source original | (1,4) | 175,824 |
| Coarse, all rows x=0,1 | (3,6) | 39,204 |
| Refined, all rows x=0,1 | (3,6) | 39,204 |
| Refined, hypothetically only x=0 | (5,14) | 10,166 |

These are exact *two-mode combinatorial counts*, not observed full
recursion performance, nor a valid active call satisfying all global
packing inequalities. They expose where a previously advertised
improvement vanishes once mode sharing is modeled correctly.

## Reproducibility and implementation boundary

`src/valuation_mode_certificate.rs` accepts a declared complete row
set, verifies the numeric crossing bit and denominator constraints on
every row, and computes the minimum. Empty or invalid support fails
closed. `valuation_modes::count_explicit_weights` reuses the source
candidate-count DP with checked arithmetic rather than duplicating it.

`tests/valuation_mode_certificate.rs` includes six independent checks:
a row-sharing counterexample; exact small-grid integer derivative
computations for the z-linear coefficient; monotonicity as rows are
added; dense-packet collapse; source-precision enumeration checked
against an independent nested loop; and invalid/overflow refusals.

Rust **1.99.1** on the separately restored `v0.19.0` source snapshot
passed `cargo fmt --all -- --check`,
`cargo test --locked --offline --all-targets`, and
`cargo clippy --locked --offline --all-targets -- -D warnings`.
acceptance gate.

## Next falsifiable experiment

Instrument the manuscript's actual *packet builder* to emit complete
target-row support sets. Compute both original and corrected mode
weights, candidate counts, and materialized child-bit costs per legal
packet/tile/Hermite point. If the complete support regularly contains
`x=y0`, the geometry-specific refinement is largely a dead end and
we should stop optimizing it. The source-uniform `a+1-i+b`
strengthening remains interesting independently.
