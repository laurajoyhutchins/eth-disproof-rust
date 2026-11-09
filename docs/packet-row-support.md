# Packet-row Hall constraints: exact pruning, but not the missing Sudoku-cell exponent

**Scope:** literal `paper` centers with the Python mode eliminator, real
`mode_catalog` descriptors and the existing `PacketEntry` coefficient
semantics. This is a stronger, source-derived **necessary** condition on
nonzero mode assignments. It does not establish a smaller worst-case
asymptotic exponent, universal completion, or `2^{o(N)}` in Sudoku cells.

Executable reference: `reference/packet_row_support.py`. TDD:
`tests/unit/test_packet_row_support.py`. Source correspondence:
`core/modes.py`, `contraction/packets.py` (`prepare_packet_terms` and
`PacketEntry._evaluate_python`), `elimination/factors.py`,
`elimination/engine.py`, and `contraction/deformation.py`.

## 1. One mode occurrence consumes one target row

Fix one packet `k`, target group `g`, and a Boolean input to its packet
oracle. The source constructs, for each target row `x`, exactly one factor

\[
  c_x + \sum_{m\in T_{k,g}:\,x\in\mathrm{rows}(m)} c_{x,m}z_m,
\]

where `T_{k,g}` is the set of modes targeting `g` from this packet.
`PacketEntry._evaluate_python` multiplies these factors and extracts the
coefficient of `prod_m z_m**beta_m`. Each factor is *linear* in the whole
family of mode indeterminates; it cannot supply two occurrences. Its
coefficient is therefore identically zero unless the requested occurrences
can be matched injectively to distinct eligible target rows.

This gives a **Hall condition**. For every subset `S` of target modes,

\[
 \boxed{\sum_{m\in S}\beta_m \le
 \left|\bigcup_{m\in S}\mathrm{rows}(m)\right|.}
\]

A sufficient condition for the *existence of a formal monomial* is a
bipartite matching of all repeated occurrences to distinct rows. It is not
sufficient for the resulting **coefficient** to be nonzero: scalar
cancellations, valuations, original vertex oracles, and the other child
factors may still annihilate it. The reference helper checks this
combinatorial condition with an independent iterative matching algorithm.
Small exhaustive tests compare matching to direct enumeration.

A cheaper necessary consequence, used by the production code, is

\[
 \boxed{\sum_{m:\,\mathrm{packet}(m)=k,\,\mathrm{target}(m)=g}
  \beta_m\le |R_{k,g}|},\quad
 R_{k,g}=\bigcup_{m\in T_{k,g}}\mathrm{rows}(m).
\]

For the source's actual geometric catalog, `R_{k,g}` is contained in the
left rows of packet `k` with group `g`; different packet/group pools are
disjoint. Summing over all packet/group pairs therefore proves another
necessary condition for the entire product of factors:

\[
 \boxed{\sum_{m}\beta_m\le M},
\]

where `M` is the parent network's number of real edges. The previous
positive-weight constraint `sum_m weight_m*beta_m < p_t` remains in force.

**Source versus target matters.** A mode appearing in the source-group
packet tensor contributes `S_b(X)**beta_m`. The source group has no analogous
row-degree restriction. Pruning that factor by the target cap would be
mathematically incorrect. The implementation applies the cap *only* to the
factor for the mode's target group.

The actual valuation-pruned mode weights also obey

\[
 w_m=(a+1-v_{\max})+b(i+1-v_{\max})\ge a+1-i+b,
\]

because `v_max<=i=v2(t)`. This floor is valid for every emitted mode, not
arbitrary invented metadata.

## 2. Exact pruning in the implemented factor builder

The new `packet_row_caps` option is **off by default** on the generic
`ModeEliminator` interface, because synthetic callback factors are not
necessarily packet coefficients. It is enabled only for the actual `paper`
`DeformationExecution` path where the `PacketEntry` semantics above hold.

At a target factor, a nonrecursive depth-first generator maintains both the
remaining positive-weight budget and the used row occurrences of each packet.
It never descends into a prefix that exceeds either budget. Every admitted
prefix can be extended by all-zero multiplicities, so total enumeration is
bounded by `O(m*A)` prefix steps when `A` bounds weighted assignments and
`m` is the mode count; it cannot increase the previous asymptotic bound.
It also guards the *actually emitted* factor assignments, not the raw
weighted count of zero-valued impossible assignments.

The old cheap first-factor preflight counts only raw weighted assignments and
could falsely refuse a `paper` center after this exact zero pruning. This
preflight is therefore bypassed only on `paper`; the real `ModeBudget`
limits still enforce work, child calls, states, terms and memory. Non-paper
paths retain the old preflight and generic factor semantics.

Independent tests demonstrate actual Cauchy packet coefficients vanishing
above the cap, compare a four-edge exact deformation to its independent
`2^(2M)` oracle, verify equal results with or without the opt-in pruning,
and establish fewer child requests (168 down to 162 in the fixture).
Synthetic factor tests check source-factor exemption, split component scopes,
and cases where the cap allows a smaller child-call budget to complete.

## 3. Critical asymptotic obstruction: Hall constraints alone are insufficient

The row restriction is real, but one must **not** infer a stronger uniform
`2^{o(s/log s)}` support theorem from it. We construct a purely symbolic
paper-admitted packing family on which even all Hall constraints retain
`2^{Omega(s/sqrt(log s))}` **admissible index assignments**.

Let `lambda=log2(s)=131072*u`, with integer `u>=8`,
`M=s=2**lambda`, `r=64`, `a=2u`, `L=2**a`. Use the previously verified
uniform-label-pair witness: one degree-one edge per ordered full-label pair,
with equally repeated classes and supplied labels. It satisfies the paper's
numerical packing hypotheses and has `P=M/L` completely full packets.
At coordinate `i=0`, exactly a `(r-1)/r` fraction of those packets have
unequal coordinate-zero labels. Thus at least

\[
 P_\times=\frac{63}{64}\frac{M}{L}
\]

packets cross. At the center `t=1`, each crossed packet has one
source-residue family `y0=0` with `L/2` common target rows, a tile
containing `j=1`, and modes at exponents `b=1,2,...,B`, each of weight
`a+1+b`. Set

\[
 B=\left\lfloor\frac{L}{16(\lfloor\sqrt u\rfloor+1)}\right\rfloor.
\]

For each of these `J=P_x B` modes, select `beta=0` or `1` independently.
Every subset obeys **every** packet Hall condition: at most `B<=L/2`
selected modes share the full target-row pool, so they can be assigned to
distinct rows. All other modes have multiplicity zero. The maximum weighted
degree is

\[
 J(a+1+B)<p_{t=1}=p_0+8\lceil3M/u\rceil L+8M(a+1).
\]

The executable witness verifies this integer inequality and every other
schedule prerequisite without allocating a network, mode catalog, or factor
table of astronomical size. Consequently **all `2**J` subsets pass the
weighted test and the full packet-row Hall test**. Since

\[
 J=\Theta\left(\frac{s}{\sqrt u}\right)
  =\Theta\left(\frac{s}{\sqrt{\log s}}\right),
\]

these two necessary tests **alone** cannot prove a uniform support bound
`2^{o(s/log s)}`. This is a lower bound on the domain passing the stated
necessary restrictions, **not** a lower bound on actual nonzero factors,
solver runtime or Sudoku difficulty. It uses supplied-label packings;
it does not prove `balanced_labels` chooses this family by default.

To close the Sudoku-cell gate with the existing `s=Theta(N log N)` encoding,
one must use stronger information than positive valuations and packet-row
capacity: e.g. algebraic dependencies/cancellations among the Cauchy modes,
structural zeros induced by the **whole** child contraction, or additional
verified constraints specific to Sudoku's input oracles. An alternative
representation or algorithm is another possibility.

## 4. Proof status

This increment neither changes native kernels nor authorizes an unbounded
fallback. The whole-frame recurrence's current conditional exponent is
unchanged. The full theorem acceptance test remains **RED**, including
non-refusal, complete bit complexity and the `2^{o(N)}` cell parameter.
