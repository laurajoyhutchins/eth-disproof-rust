# One recurrence for the paper contraction: a conditional closure, not a solver theorem

**Status: the current implementation does not have a complete non-refusing
worst-case bit-operation theorem.** The executable companion is
`reference/whole_frame_recurrence.py`; its checkpoint tests are
`tests/unit/test_whole_frame_recurrence.py`. The earlier explicitly red
`research_acceptance/test_complete_bit_recurrence.py` must remain red.

This note integrates previously separate local bounds into one recurrence and
names the premises for which a complete implementation-to-proof correspondence
is still missing. It never uses the runtime resource caps as complexity lemmas.
The scope is the **literal paper schedule, Python mode elimination, eager
canonical `Padic` arithmetic, and interpolation recovery**; optional native,
lazy and experimental-jet paths are not covered.

## 1. A center has a bounded mathematical domain

Let `s` be the paper's network-size parameter, `lambda=ceil(log2 s)`,
`M_d,V_d,p_d` the path envelopes for edges, vertices and precision at depth
`d`. Put `a_d` and `u_d` equal to the literal schedule and `L_d=2**a_d`.
The conditional packing lemma gives `P_d L_d <= 3 M_d`. For evaluated
centers with valuation `i<u_d`, define

\[
 h_d=\lceil3M_d/u_d\rceil,\qquad
 p_{d,i}=p_d+8h_d L_d/2^i+8M_d(a_d+1),\qquad
 K_{d,i}=P_d 2^{i+1}.
\]

The actual catalog has **at most one mode per positive integer weight** for
any packet and `y0`; the newer valuation-aware mode weights remain strictly
increasing with its exponent `b`. The global positive-weight budget bounds
the number of local or projected mode assignments by

\[
 A_{d,i}< 2^{4\sqrt{K_{d,i}p_{d,i}}}.
\]

The crucial point is **not** to multiply the independent maxima of `K` and
`p`: the precision taper cancels their opposing powers of two. Uniformly,

\[
 K_{d,i}p_{d,i}
 \le P_d2^{u_d}(p_d+8M_d(a_d+1))+16P_dh_dL_d.
\]

Write `alpha_d` for four times the integer ceiling of the square root of
that upper bound. At one deformation, there are at most
`F_d=64(V_d+P_d+1)` factor components and at most `A=2**alpha_d`
mathematical weighted assignments per factor. There are at most
`E_d=M_d(2L_d-1)+1` interpolation samples per center and at most
`C_d=2L_d-1` nonzero centers. Consequently the number of *recursive child
contractions started by one parent call* is bounded by

\[
 B_d\le C_dE_dF_d2^{\alpha_d}.
\]

This upper bound **does not contain** `ModeLimits.max_child_contractions`.
That configuration parameter can make a run refuse: it cannot be used to
establish that the same run is fast *and finishes*. The tests explicitly
verify that the mathematical fanout ceiling exceeds the configured budget.

## 2. The local work must include every operation that surrounds a child

The following terms are separately accounted by existing reference models
and combined by the new helper. These are constructive **conditional
schoolbook bit-operation models**, not measured CPython or FLINT instructions.

| Local term | Source of the conditional ceiling | What it excludes |
| --- | --- | --- |
| Factor rows, joins, projections, sparse polynomial convolution | `center_evaluation_work.py`, positive-weight support and `nested_ring_bit_cost.py` | Hashing, ordering and unmodeled representations |
| Child geometry and preparation | `packet_preparation_work.py` multiplied by **uncapped** mathematical child fanout | Recursive child contraction itself, native/lazy code |
| Shared Cauchy setup and cross coefficients | `cauchy_context_calls` and per-child preparation model | Noncanonical oracle arguments |
| Newton interpolation | `bit_work.py`'s exact ring-call envelope and canonical `Padic` bit costs | Cost of producing each point sample, charged above |
| Tapered Hermite rational recovery | `recovery_bit_work.py` schoolbook model | Center coefficients, charged above |
| Terminal direct summation | At most `2**M_terminal` assignments | Guaranteed completion of the current limited leaf implementation |

These counted pieces form `U_d^(named)`. Their sum is bounded explicitly
without allocating `2**alpha_d` assignments. The **numeric value is NOT a
complete `U_d`** because it omits the outstanding source-level premises
below. In particular it would be incorrect to put `U_d^(named)` into the
existing red acceptance test as an unconditional bound.

The skeleton is

\[
 T_d\le U_d+B_dT_{d+1},\qquad B_d\le C_dE_dF_d2^{\alpha_d},
\]

but the implementation currently has no certified upper bound for the whole
`U_d` or a successful termination policy. The helper can unfold a
**counterfactual** recurrence assuming all missing local source operations
cost at most `(s+1)**c` bit work and every bounded leaf is replaced by a
total exact implementation. This method is deliberately called
`hypothetical_polynomial_glue_log2_bound`, and
`require_complete_theorem()` always rejects the current missing premises.

## 3. The recursion depth and the early terminal cases both matter

A paper-active call has

\[
 u_d=\left\lfloor\frac{\lambda}{131072\,2^d}\right\rfloor>0,
 \quad a_d=2\sum_{j\le d}u_j,
\]

so there are at most `O(log lambda)` active depths, and all constructed
children obey `M_(d+1)<=floor(3M_d/32)` **provided the packing premises
hold**. An ordinary leaf has `M<=H=ceil(s/sqrt(lambda))`, while the end
of the active schedule has `M<=s(3/32)^D`.

The source has a *third* route: if one of the numerical packing
preconditions fails, it selects the leaf before packing. It is not free.
The failed inequalities imply, using `D_d=64**(2a_d)` and the paper degree
bound `Delta<=ceil(s**(9/10))`, that its `M` is below either
`2 D_d**2 Delta` or `L_d D_d`. The missing inequality `2L<=Delta`
is automatic for paper-active `lambda>=131072`. Thus every reachable leaf,
including a numerical-exception leaf, has a **conditional** edge ceiling

\[
 M_{\rm leaf}\le\max\{H,\;s(3/32)^D,\;
     2D_{\max}^2\lceil s^{9/10}\rceil,\;L_{\max}D_{\max}\}
    = O(s/\sqrt{\lambda})
\]

as `lambda` tends to infinity. The source helper uses exact integer upper
bounds for the degree term. The statement above concerns the mathematical
base case *if it can be computed*, not the present `LeafConfig.limit` and
`max_width` which explicitly refuse valid instances.

## 4. Conditional asymptotic composition: a limit, not a finite benchmark

The existing global-support proof gives a uniform ratio
`K_(d,i)*p_(d,i) <= B_lambda*s**2`. To make the **depth composition**
explicit, its symbolic expression satisfies

\[
 B_\lambda = O(\lambda^{-1/2}).
\]

One elementary bound splits depths at
`d=floor((log2 lambda)/2)`. Before this split `u_d=Omega(sqrt(lambda))`,
so the factors `2**(-u_d)` beat the polynomial-in-`lambda` schedule
terms; the terms proportional to `1/u_d` are `O(lambda**(-1/2))`.
After this split `(3/32)**d <= O(lambda**(-gamma/2))` with
`gamma=log2(32/3)>3`; the terms containing `lambda*(3/32)**d`
and `(3/32)**(2*d)` are also `O(lambda**(-1/2))` or smaller.

Therefore `alpha_d <= 4*s*sqrt(B_lambda)+O(1)
=O(s/lambda**(1/4))`, **uniformly across every active depth**.
If `V_0`, initial names and initial coefficient precision have polynomial
size in `s`, the explicit prefactors in the counted local work have
polynomial bit size. If the still-unproved glue terms are also polynomial,
then the `O(log lambda)` nested levels and the terminal leaf yield the
**counterfactual** bound

\[
 \log_2T(s)
 \le O\left(\frac{s\log\lambda}{\lambda^{1/4}}
               +\frac{s}{\sqrt\lambda}+\mathrm{polylog}(s)\right)
 =o(s).
\]

This is a **conditional derivation**, not a theorem about the current
implementation. Especially at the first paper-active
`lambda=131072`, the conservative exponent can be *much larger* than `s`.
The tests never assert finite-parameter `log2(T)<s` as a substitute for the
asymptotic proof.

## Oracle descriptor and inherited-name accounting (new local closure)

`reference/oracle_lineage.py` now checks the source-level invariant for
both direct and compiled child construction: retained vertex oracles are
identical callable references, not recursive wrappers, and new packet
oracles are locally prepared `PacketEntry` objects. For one successful
paper path, nonempty packet ownership and the live `3M/32` child shrinkage
give

\[
V_d\le V_0+\lfloor 32M_0/29\rfloor.
\]

New source-generated names are precisely `packet:{k}:g{group}`, where
`k<M_0` and `group<64`. With `D_0` bits of input vertex names, their
aggregate visible UTF-8 name payload is at most

\[
D_d\le D_0+
 8\lfloor32M_0/29\rfloor
 (15+\max(1,\operatorname{bitlength}(M_0))).
\]

`assemble_paper_recurrence` now passes this path-wide name bound into
**every** child preparation cost envelope. Previously it reused only
`D_0` at subsequent depths, which could undercount generated packet
names. The model exposes both descriptor and name-bit ceilings, and
refuses to derive a valid theorem from them alone.

These bounds concern **one execution path's visible references and name
strings**, not the total number of sibling child constructions, transitive
object memory, or the cost of invoking inherited arbitrary callbacks. They
do not eliminate the original input-oracle cost premise. See
[oracle-lineage-proof.md](oracle-lineage-proof.md).

## 5. Missing certificates and concrete negative evidence

The integrated proof checker reports these **unclosed** obligations:

1. A uniform bit-cost contract for *all* inherited oracle invocations.
   The canonical direct Sudoku encoder now uses immutable, fixed-program
   `CellEntryOracle` and `UnitEntryOracle` callbacks. The source-checked
   `reference/sudoku_oracle_cost.py` gives a polynomial **one-pass** bound,
   and the inherited descriptor/name bound is established along a successful
   paper path. The outstanding obligation is to bound the *total number*
   of original callbacks across each local frame, as well as arbitrary
   `Network` callbacks. These may not be charged as free operations.
2. Source-to-proof correspondence for all packing, component partitioning,
   factor planning, mode ordering and allocation/hash work. The local
   envelopes count arithmetic but do not certify all language-runtime work.
3. The corresponding proof for any selected native/lazy kernels, or a
   correctness-preserving explicit choice of the analyzed Python reference.
4. A complete terminal policy for both ordinary and numerical-fallback
   leaves, which never mistakes `CapacityError` for an answer.
5. Removal or safe size-dependent replacement of **all** finite mode,
   leaf, cache and factor budgets. Current budgets can and do refuse.
6. A complete peak-bit-memory bound including shared objects, retention,
   cache ownership and intermediate allocations (not estimated RSS alone).
7. The input-parameter distinction: with direct Sudoku encoding
   `s=M=Theta(N log N)` for `N` cells, **`2**o(s)` is not by itself a
   proof of `2**o(N)`** in cells. Nor does it establish an ETH conclusion
   without an appropriately parameter-preserving reduction.

There is already a real empty 4×4 Sudoku for which the literal paper
schedule refuses its terminal leaf at the default capacity. The new
checkpoint tests exercise that case *as an unresolved theorem obligation*;
they do not mark refusal as a solved instance.

### Verification and next action

Run:

```bash
PYTHONPATH=src:. python -m pytest -q tests/unit/test_whole_frame_recurrence.py
PYTHONPATH=src:. mypy --strict reference/whole_frame_recurrence.py
PYTHONPATH=src:. python -m pytest -q research_acceptance/test_complete_bit_recurrence.py
```

The last suite is **intentionally red**. The fastest way to settle the
presently unproved recurrence premise is to define a proof-carrying,
size-parameterized *total leaf and resource policy*, then verify it
against the existing live branch/packing/precision envelopes. Until that
happens, further constant-factor kernel tuning does not close the theorem.
