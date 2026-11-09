# Rational Hermite recovery: a conditional bit-cost lemma

**Scope:** the actual `StreamingHermite` and `tapered_recover_over_ring` routines, **after exact center jets have been supplied**. The production solver is unchanged. `reference/recovery_bit_work.py` implements the symbolic cost model and `tests/unit/test_recovery_bit_work.py` verifies it independently, including a real `Padic`-method dispatch trace. The complete-solver theorem acceptance test remains **RED**.

## Center schedule

Set `L=2^a`, `h=ceil(3M/u)`, `q_t=h max(0,u-v2(t))` for `t in [-L,L)\{0}`, and let `Q=sum_t q_t`, `C=# {t:q_t>0}`, `q_max=max_t q_t`. The center precision is exactly

\[
p_t=p+8h\,L/2^{v_2(t)}+8M(a+1),\quad p_*=\max_t p_t.
\]

There are `L/2^i` centers of valuation `i<a`, and one of valuation `i=a` (`t=-L`). The helper computes these **symbolically**, without allocating the O(L) center dictionary, any coefficient rings, or any jets. Tests compare against direct center enumeration and the independent paper precision envelope. At paper-admitted centers `a>=2u`, so the exceptional endpoint `t=-L` is inactive.

## Exact Fraction numerator/denominator bounds

The implemented normalizations and degree-dependent scales are

\[
A_t=\prod_{s\ne t,\,q_s>0}\left(\frac{-s}{t-s}\right)^{q_s},
\qquad \sigma_{t,j}=A_t\left(\frac{-t}{2L}\right)^j,
\quad 0\le j<q_t.
\]

Each base fraction's numerator and denominator have magnitude at most `2L`. Let `H=1+(a+2) max(0,Q-1)`. The numerator and denominator of **every intermediate normalization and scale** have at most `H` bits. This follows by multiplying unreduced numerators and denominators; canonical `Fraction` reduction cannot increase their widths.

Assume each flattened center coefficient is canonical: an integer in `[0,2^p_t)`. Each accumulated term `sigma[t,j] * coefficient` then has numerator width at most `H+p_*` and denominator width at most `H`. A coordinate of `answers` is the sum of at most `Q` such terms. Using the product of their denominators gives a common denominator, and bounding the sum of unreduced numerators proves for **every prefix**, not only the final sum:

\[
\begin{aligned}
\operatorname{bits}(\text{denominator}) &\le 1+QH,\\
\operatorname{bits}(\text{numerator}) &\le 4+p_*+H+QH+\lceil\log_2(Q+1)\rceil.
\end{aligned}
\]

Independent tests reproduce all normalizations and accumulate the maximum possible canonical coefficient at each center, checking the bound after *each* addition. These tests also check the actual polynomial-recovery result against its known exact count. Reducing the rational sum modulo `2^p` before it is complete would be mathematically unsound.

## Loop bounds and schoolbook bit operations

The source's outer operation counts are bounded by:

| Work | Maximum |
|---|---:|
| Normalization factors | `C(C-1)` |
| Binomial coefficients and ring powers | `(C-1)Q` |
| Truncated unit-series convolution pairs | `(C-1) Σ_t q_t²` |
| Reciprocal-series pairs | `Σ_t q_t(q_t-1)/2` |
| Quotient convolution pairs | `Σ_t q_t(q_t+1)/2` |
| Exact `Fraction` powers | `C(C-1)+Q` |
| Exact `Fraction` accumulator additions | `D Q` |

Here `D=e product(q_i)` is the number of scalar coordinates in the existing outer coefficient ring. **For the literal paper schedule, D=e**, because it uses `Padic` interpolation, not `JetRing` recovery. The helper also charges `Padic.rational` conversions, the `math.comb` integer operations, center-dictionary scans, and `Padic.pow`'s inner arithmetic via the previously proved schoolbook ring model.

The bit model uses quadratic schoolbook integer multiplication/division, cubic Euclid/gcd envelopes, binary exponentiation, and O(j) integer multiply/divide steps to compute `comb(m,j)`. This is a constructive algorithmic bound, **not** a verified count of the precise CPython, FLINT or Cython native instructions. `schoolbook_bit_work_majorant` evaluates a deliberately loose numeric accounting formula in this stated model; it is not a proof object for machine-time cost.

## Retention

The rational answer vector retains `D` numerator/denominator pairs of the above bit widths. The current center's canonical arrays require `O(q_max D p_*)` payload bits, and the dictionary of center orders has at most `2L-1` integer entries. The helper reports both `center_payload_bits` and a broader `retained_abstract_payload_bits`, but **neither is process RSS**. Real Python object and allocator overhead, native objects, and global solver caches remain outside this lemma. The eager caller additionally retains all supplied center jets, requiring up to `Q D p_*` canonical payload bits, reported separately as `eager_input_payload_bits`.

## The asymptotic conclusion and its limits

On a successful paper path with `M_d<=s`, `p_0<=s`, `e=O(log s)` and `a_d<log_2(s)/32768`, we have `L_d=O(s^(1/32768))`, `Q=O(M_d L_d)=O(s L_d)`, and the proved conditional precision envelope gives `p_*=s^O(1)`. Thus:

\[
H=O(Q\log L),\qquad
\operatorname{bits}(\mathrm{answers})
=O(p_*+Q^2\log L)=s^{O(1)}.
\]

All listed loop counts and arithmetic operand widths are polynomial in `s`, hence **one rational recovery stage has polynomial bit work and polynomial abstract payload** in the specified schoolbook model, conditional on the stated source/precision assumptions. Symbolic-size checks verify the actual integer schedule at enormous sizes; finite checks are regressions, not a substitute for the asymptotic derivation.

The following remain unresolved:

1. Producing the **center jets** by deformation evaluation and Newton interpolation, including the bit costs of globally joined mode factors and recursively generated oracles.
2. Guaranteeing every initial and recursively constructed oracle emits canonical coefficients with the required precision and uniform cost.
3. The costs of irreducible-modulus search and native backend correspondence, and full process memory with all factor tables, caches, and generated children.
4. Non-refusal for all generalized Sudoku inputs and the full recurrence, especially translating network-size `2^o(s)` to cell-size `2^o(N)` when `s=Theta(N log N)`.

Run `PYTHONPATH=src:. python -m pytest -q tests/unit/test_recovery_bit_work.py`. Do **not** mark the red research acceptance test as passed because this local lemma is now established.
