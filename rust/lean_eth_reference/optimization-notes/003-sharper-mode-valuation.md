# Optimization experiment 003: use the full proved 2-adic mode valuation

**Status:** conditional algebraic pruning rule and locally executed model.
Not yet wired into the original tensor-contraction engine.

**Source:** [quantitative-contraction.tex](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex), labels `eq:tensor-mode-expansion` and `eq:tensor-mode-budget`, exact blob `51ba54efc29f51bbc0426f848003030da484f354`.

## The unnecessary work

For a mode of geometric exponent `b` at a crossing tile of valuation
level `i`, the original proof assigns weight `w = b+1` and retains
every multi-index beta with `sum(beta*w) < p_t`. But the preceding
derivation establishes both:

- `v2(C(T)/(C'(0)*(T-y0+x))) >= a+1-i`;
- `v2((2^(i+1)/(T-y0+x))^b) >= b`, since the crossing condition
  gives `v2(T-y0+x) <= i`.

Therefore **every occurrence** of that mode has valuation at least

```text
w_sharp = (a + 1 - i) + b   >=   b + 1 = w_original.
```

For a product of mode coefficients, valuations add. If the sum of
beta-weighted guaranteed valuations reaches precision `p_t`, its
coefficient is zero modulo `2^p_t`. We may omit that tuple *locally,
at that precision* without changing the contraction in the working ring.

The condition `i <= a` and the crossing valuation inequality are
**preconditions**, not properties inferred by this Rust module. The
kernel rejects `i > a`; integration must additionally establish the
actual crossing condition from source geometry.

## Replacement and representation

The experimental Rust module `src/valuation_modes.rs` offers two
policies (source-original and stronger), a checked, bounded enumeration
of the exponent tuples, and a separate generating-function DP that
counts the candidate set without enumerating it. It is isolated from
the literal BitProgram machine and does not replace the tensor
coefficient extractor.

For eight equal modes with `b=0,a=20,i=7,p=32`, the candidate count
decreases from **61,523,748** to **45**. This is exact combinatorial
counting, not a timing result or a representative full ETH instance.

## Evidence and refusal

- A test enumerates both policies and verifies the stronger set is
  contained in the original for small precision budgets.
- A modular arithmetic test assigns coefficients divisible by the
  claimed powers of 2, checks every deleted monomial is zero modulo
  `2^p`, and checks the total original and truncated sums agree.
- Count DP and actual iterator counts agree; overflow, invalid
  valuation levels and explicit experimental resource budgets refuse.
- Rust 1.99.1 passed these four tests plus strict Clippy and rustfmt on
  the separately restored v0.19 snapshot. Exact combined branch CI,
  original Lean execution, and real tensor-contraction integration
  remain unverified.

## What this does not prove

This refines an *existing upper bound*, not the asymptotic theorem.
It does not show large savings at actual source parameters, does not
prove a smaller worst-case exponent, and does not account for child
tensor construction, arithmetic bit lengths, or canonical lifting
across recursion. Those operations require their own correctness and
resource checks.

**Next:** instrument actual packet mode weights and `p_t` in the
original contraction code; compare both candidate counts before
turning the stronger rule on. Only integrate it when the coefficient
valuation and precision-lift contracts are established.
