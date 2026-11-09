# Canonical finite-ring bit costs and nested Taylor coefficients

**Scope: a conditional arithmetic lemma, not a completed worst-case solver bound.**
The executable model is `reference/nested_ring_bit_cost.py`; its regression
checks are `tests/unit/test_nested_ring_bit_cost.py`. No solver arithmetic
implementation is modified. The abstraction uses binary schoolbook addition,
multiplication, and polynomial reduction with explicitly charged temporary
integer width. It is not a count of CPython instructions, an upper bound on
arbitrary compiled FLINT/Cython implementations, or a prediction of wall time.

## 1. The necessary finite-input premise

Let

\[
R_{e,p}=\bigl(\mathbb Z/2^p\mathbb Z\bigr)[U]/(f(U)),
\qquad \deg f=e,
\]

with a **supplied**, verified monic binary modulus `f` whose reduction modulo
2 is irreducible. Each value must be a length-`e` tuple of integers in
`[0,2^p)`. With nested truncated Taylor variables of lengths
`q_1,...,q_h` (innermost first), every outer tuple has exactly the
corresponding `q_i` children. In particular, a vertex oracle returning an
unbounded Python integer is **not** covered by this lemma.

`canonical_value` checks the premise and `canonical_cost_envelope` refuses
noncanonical values; these checks are not assumed to be free when included in
a real algorithm. We do not silently replace a high-bit input with its modular
remainder and then claim its processing cost was bounded by `p`.

## 2. Base coefficient work

A canonical `Padic` addition, subtraction, or negation performs `O(e)`
operations on `O(p)`-bit integers. Schoolbook multiplication convolves at
most `e^2` input-coefficient pairs and reduces at most `e-1` high-degree
terms using a monic binary modulus. The integer magnitudes in its temporary
convolution are bounded by `O(e*2^(2p))`, hence their bit width is at most

\[
B=2p+\lceil\log_2(e+1)\rceil+O(1).
\]

Consequently, with a supplied `f` and canonical inputs,

\[
A_0=O(ep),\qquad
M_0=O(e^2 B^2).
\]

The reference inverse first constructs the residue-field inverse in
`GF(2^e)` with `O(e)` carryless modular products of `O(e^2)` bit cost,
then applies exactly `p.bit_length()+1` Newton rounds of two coefficient
multiplications and one subtraction, followed by an inverse-identity check.
This gives

\[
I_0=O(e^3+(1+\log p)M_0).
\]

The implementation's explicit conservative integers use larger fixed
constants and, when needed, an additional factor in `e`. They are deliberately
loose constructive **schoolbook-model ceilings**. The proof does not assert
that native backends use those exact routines. Negative powers add one
inverse, and any exponent of bit length `b` requires at most `2b`
ring multiplications plus exponent-bit bookkeeping.

**Excluded at this boundary:** searching for an irreducible `f`, external
integer construction, rational conversion from arbitrarily large numerators,
validation of arbitrary callbacks, native allocation and operations, and
reference vs. native dispatch selection. These costs must be charged by their
own theorem obligations.

## 3. Nested Taylor arithmetic is a recursive cost model

Let `C` be the coefficient ring beneath one `JetRing(C,q)`. Write `A_C`,
`M_C`, `N_C`, `I_C` for worst-case schoolbook add, multiply, negation, and
inverse work on canonical values. With `D_C` the stored coefficient payload
and `H(q,C)=O(q^2(D_C + tuple_nodes(C)+log(q+1)))` for scanning,
comparison, indexing and tuple construction, the **actual Python algorithm's
loop structure** gives

\[
\begin{aligned}
A_q &\le q A_C+H(q,C),\\
N_q &\le q N_C+H(q,C),\\
M_q &\le \frac{q(q+1)}2(M_C+A_C)+H(q,C),\\
I_q &\le I_C+\frac{q(q-1)}2(M_C+A_C)
            +(q-1)(M_C+N_C)+H(q,C).
\end{aligned}
\]

The triangular multiplication bound is valid even for all-dense operands.
Zero skipping can only decrease the number of pairwise coefficient updates.
Inverting a jet recursively inverts its constant coefficient once, followed
by the displayed triangular coefficient recurrence. A TDD counterexample
caught an accounting error here: a `Padic.inv` inside `JetRing.inv` performs
its *own* Newton multiplications. The corrected test charges both levels.

These bounds do not use measurements to infer asymptotic rates. Their
correctness depends on the canonical-value premise and the specified
reference routines. `pow_bits(n)` charges the exponent's bit length and
includes inversion for negative exponents.

## 4. Representation size and temporary storage

For `h` nested jets, a dense **canonical value's integer payload** is
exactly

\[
D_h=ep\prod_{i=1}^h q_i\quad\text{bits of fixed-width coordinate capacity}.
\]

The corresponding full tuple-tree has exactly

\[
H_0=1,\qquad H_i=1+q_iH_{i-1}
\]

tuple nodes (not including the scalar integer leaves). For example, with
`q=(2,3,4)`, this is `1 + 4 + 4*3 + 4*3*2=41` tuples. Values whose
coefficients are zero or shared may use fewer distinct Python objects.

`temporary_payload_bits` propagates a **loose structural allowance** for
simultaneously live coefficient vectors and the innermost arithmetic
scratch. It excludes pointer widths, arbitrary native allocations, allocator
bookkeeping, cache ownership, the number of retained factor rows, and all
rational recovery objects. It must not be reported as process RSS or the
solver's peak-bit-memory theorem.

If `e,p` are polynomial in a growing parameter `s`, there are at most
`O(log s)` Taylor layers, and each `q_i` is polynomial in `s`, the product
`prod(q_i)` is at most `2^{O((log s)^2)}`. Consequently the arithmetic
recurrences are **conditionally subexponential** in `s`. This conditional
statement requires independent proofs of those parameter bounds for any
solver path to which it is applied.

## 5. Most important: the literal paper solver does not use JetRing

`ContractorConfig.__post_init__` rejects `recovery.method='jet'` for
`schedule='paper'`; this is tested. The literal paper path uses polynomial
interpolation over a `Padic` ring and exact rational recovery.

`paper_padic_bit_envelopes` therefore propagates **only base-ring**
reference costs along the allocation-free paper precision envelope. It
checks symbolic schedules at `lambda=131072` without constructing the
astronomically large extension ring or executing the algorithm. Conditional
on the previously derived `e=O(log s)` and `p=s^{O(1)}` along every
successful path, each *individual schoolbook Padic operation* costs
`s^{O(1)}` bit operations and has polynomial canonical coefficient size.
This discharges one arithmetic sub-lemma, not the count of such operations.

The paper's **remaining** bit-cost obligations are more important:

1. Account for *how many* arithmetic operations the actual mode elimination,
   packet preparation, and recovery routines execute, including hashing,
   state scans, integer powers and materialization costs.
2. Bound exact rational numerator/denominator growth and the number of
   operations in `tapered_recover`; the Padic bound cannot be substituted for
   `Fraction` arithmetic.
3. Include modulus construction and a uniform bit-cost contract for original
   input oracles. Native kernel paths need their own cost correspondence or
   an explicitly selected reference implementation.
4. Prove totality/non-refusal on the declared input family and compose the
   complete resource recurrence. An intermediate bound for one arithmetic
   operation is never a total bit-time bound.
5. Convert the result from Boolean network size `s` to Sudoku cells `N`
   without silently assuming `s=O(N)` for the current direct encoding.

The opt-in theorem test
`research_acceptance/test_complete_bit_recurrence.py` **remains red**.
