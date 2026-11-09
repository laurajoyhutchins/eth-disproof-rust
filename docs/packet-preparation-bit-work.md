# Packet preparation and child construction: conditional bit-work bound

**Status:** local cost bound for a *single* paper-schedule deformation sample,
not completion of the recursive counting theorem. The source-correspondence
model is `reference/packet_preparation_work.py`, tested independently in
`tests/unit/test_packet_preparation_work.py`. Both the direct
`make_child` implementation and the compiled-topology instantiation path
are included. No production solver code has been modified.

## Premises and boundaries

Let a validated parent network have `M` edges, `V` vertices, at most `P`
packets of width `L=2^a`, `m` cataloged modes at one evaluated center,
`e` extension coordinates and `p` precision bits. Assume:

1. **Paper packing:** `P*L <= 3*M`, with distinguishable edges packed exactly
   once and the child-shrinkage and center-precision premises already proved
   for the invoked paper schedule.
2. **Paper mode catalog:** its `y0` loop has at most `L` entries per packet
   (the engine does not catalog the excluded `t=-L` center); its `b` loop has
   at most `p-1` entries. Consequently `m <= P*L*(p-1) <= 3*M*(p-1)`.
3. **Finite, bounded descriptions:** all parent vertex names have an explicit
   total `D`-bit encoding bound. Input and inherited callbacks may be *held
   by reference*, but their unknown internal evaluation work is excluded.
   Names grow by at most a fixed prefix per construction generation, so with
   polynomial `D` and at most `O(log s)` active recursion levels, names
   remain polynomially bounded.
4. **Canonical eager reference `Padic` arithmetic:** no native packet kernel,
   lazy expression-DAG coefficients, or unproved user-supplied ring ABI.
   The irreducible modulus is already supplied. Those alternate backends
   require separate implementation-to-model correspondence.

A computation that refuses due to a capacity guard is not a successful
algorithm under the claimed theorem. The premises do **not** establish
non-refusal.

## Exact outer ring-call budgets

For the active, nonzero `t` in `(-L,L)`, the shared `EvaluationContext`
constructs `cauchy_values` once per deformation evaluation. Actual source
loop counts, independently traced using a delegating `Padic` spy, are:

| Operation | `L=2` direct fast path | `L>=4` prefix/suffix path |
| --- | ---: | ---: |
| `scalar` | 10 | `6L-2` |
| `add` | 3 | `2L-1` |
| `mul` | 18 | `14L-5` |
| `inv` | 1 | 1 |
| `pow` | 0 | 0 |

The numerator `cauchy[t]` is shared, not recomputed for each cross mode.
Each *cache miss* in `EvaluationContext.cross_coefficient(x,y0,b)` executes
**exactly** four `scalar`, one `add`, six `mul`, one `inv`, and one `pow`.
A cached hit invokes none of these. This counts *outer* ring calls: `inv`
and `pow` are charged separately by the canonical Padic schoolbook model.

Across one uncached child preparation, each of at most `P` entries has at
most `L` target rows and at most `m` candidate target modes. Hence

\[
R_{\mathrm{cross}}\le P L m.
\]

The bound remains valid if the context cache misses on every request,
although normal center-local reuse reduces actual ring work. The mode
constructor's exponent satisfies `0 <= b <= p-2`, so one `Padic.pow`
requires at most `O(log p)` coefficient multiplications.

The common Cauchy odd denominator has at most `2L-1` factors, each of
absolute value `<=L`, so its *pre-modular-reduction* bit width is
`O(L log L)`. Other direct scalar inputs and exponents are bounded by
`O(p+L log L)` bits. No inverse of an even 2-adic element is taken by
these formulas under their recorded source-side valuation checks.

## Construction and descriptor work

`make_child` builds owner/slot maps and the retained port incidence;
`CompiledChildPlan` can reuse that topology. In the worst-case uncached
path, each packet's geometry materializes at most `L^2` row/right-position
pairs; preparing terms compares at most `L*m` target candidate pairs and
may perform up to `L` membership comparisons per pair. The source-mode
tiles contain at most `m*L` entries per packet. A conservative bound on
integer/index work is

\[
O\!\left(M+V+PM+P L^2(m+1)+P Lm+D\right),
\]

where ordinary index comparisons have `O(log(M+V+P+L+m+p))`-bit values.
The independently computed `PreparedChildWork` includes a loose cubic
schoolbook-bit majorant for metadata, odd denominator construction,
and all cross ring calls, plus a separate catalog scan count.

`mode_catalog`, evaluated once per center valuation unless cached,
constructs at most `P*L*(p-1)` modes. For one packet it scans at most
`O(L^2)` tile/row candidates, and copies at most `O(L)` metadata per
mode. This has `O(M+P L^2 p)` structural index work and polynomially
bounded integer representations.

The model reports scalar payload slots in a prepared child, rather than
claiming to measure retained RSS or the transitive ownership of shared
networks, contexts, compiled plans, and Python callback closures.

## Asymptotic consequence, conditional on earlier paper lemmas

The prior paper-schedule analysis supplies `M<=s`, `V=s^{O(1)}`,
`L=O(s^(1/32768))`, `p=s^{O(1)}`, and `e=O(log s)` along successful
active paths. Hence `P<=3s/L`, `m<=3s*p`, `D=s^{O(1)}` for the chosen
well-described input encoding. Every construction/count term above is
polynomial in `s`; so **one paper child preparation and one Cauchy context
have polynomial abstract bit cost** under the specified schoolbook model.

Combining this with a previously established *subexponential number* of
per-center admissible child evaluations does not require cheap child
contractions. The child contraction cost must be represented by the
recursive term `K_d T_{d+1}`. What is discharged here is only the
**nonrecursive preparation cost per invocation**, not `T_{d+1}` itself.

## TDD evidence

`tests/unit/test_packet_preparation_work.py` independently instruments
`Padic` calls for `L=2,4,8` and two signs of the center, checks distinct
cross-key misses versus cache hits, prepares real child networks with
both direct and compiled paths, compares their packet-oracle values for
all small bit assignments, verifies symbolic polynomial-size family
bookkeeping, and refuses malformed packet counts, catalog sizes,
precisions and unspecified metadata widths.

## Outstanding red obligations

- Local factorization planning, elimination ordering and memory ownership
  still require a complete *whole-frame* accounting, rather than standalone
  operation models. Compiled-plan cache retention and native/lazy kernels
  are different operational paths.
- Input and inherited vertex-oracle evaluation cost is not replaced by
  a source-code scan: callbacks must satisfy a uniform cost contract.
- The `paper` base-case leaf policy still refuses valid small networks,
  and finite budgets for modes/memory/children are not proved sufficient.
- Even a complete `2^{o(s)}` theorem in Boolean-network edges does not
  imply the desired `2^{o(N)}` theorem in Sudoku cells for the current
  `s=Theta(N log N)` direct encoding.

**Keep `research_acceptance/test_complete_bit_recurrence.py` RED.** Do not
put invented upper bounds into its acceptance dictionary merely because
this local preparation bound has now been discharged conditionally.
