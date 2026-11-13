# Optimization experiment 007: paired packet slots collapse geometric mode weights

**Status:** source-structure deduction and six executable tests. The generic
occupancy model is not a reproduction of the original collision-packing
algorithm; it explicitly assumes the three structural properties of its
output and checks their consequences. No live tensor contraction is sped up
yet.

**Pinned source:** [quantitative-contraction.tex](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex), blob `51ba54efc29f51bbc0426f848003030da484f354`;
Lemma `tensor-packets`, subsection `tensor-modes`, equation
`tensor-mode-expansion`, and subsection `tensor-children`.

## The original structure matters more than individual valuations

Lemma `tensor-packets` states that **each real edge occupies the same
slot on the row and column sides**. For each coordinate i with unequal
symbol labels, the slot's ith bit determines the symbols' orientations.
In that case the mode construction says a row x and a column y are in
different groups **iff their ith slot bits agree**.

Let `i=v2(t)<u`. A mode Z is indexed by one packet, a column tile
`y=y0+2^(i+1)*j`, and geometric exponent b. Suppose its source tile
has at least one real column y. The same real packet edge has a **real
row at slot x=y**. Its ith bit equals the tile's ith bit, so this row
belongs to the mode's contributing target rows. For that row,

```text
d = t-y0+x = t+2^(i+1)*j,
v2(d)=v2(t)=i.
```

Experiment 006 established the safe whole-mode weight as the minimum
over all contributing rows of

```text
(a+1-v2(d)) + b*(i+1-v2(d)).
```

Every crossing row has v2(d)<=i, giving weight >=a+1-i+b. The paired
row x=y **attains equality**. Therefore for every genuinely nonzero
source mode from this packet construction:

```text
boxed:  w_Z,geometric = a+1-i+b.
```

This is a **negative research result** for the extra per-row refinement
in experiments 005 and 006. It is stronger than the previous
"dense-packet" observation: even an arbitrarily sparse packet with
just **one real source column** forces the coarse bound. The earlier
single-row example offering weight 14 where the source-wide bound was 6
cannot arise as a complete source mode with a real column and an
unpaired row.

It does **not** eliminate the improvement from the manuscript's
published `b+1` weight to the source-derived uniform
`a+1-i+b`. That bound still deserves real integration and
bit-complexity evaluation. Cancellation of row coefficients might
also create further instance-specific divisibility, but that is a
different claim requiring a different certificate.

## A second, positive, exact simplification

The manuscript explicitly states that if a mode's source tile has no
real column, then `L_Z(X)=0`. Every term with `beta_Z>0` vanishes
and `beta_Z=0` contributes the identity. Therefore an enumerator may
**delete that mode variable before constructing candidate tuples**,
provided it knows the complete real-column occupancy.

The Rust module `packet_mode_support.rs` takes a validated unique
real-slot set, coordinate labels, point t and a source tile. It
distinguishes:

- equal-symbol packets, where all terms are local;
- empty source tiles, which have zero mode forms;
- contributing tiles, whose target rows come from the *same* real
  slots and whose whole-mode weight is proved to equal `a+1-i+b`.

This is a conditional adapter over source packing output, not a new
standalone proof that the packet label assignment was constructed
correctly. Empty/inconsistent/invalid evidence fails closed.

For one packet with `a=4,u=3,t=4`, and only real slot 9,
there are eight possible residues `y0=0..7` but just one nonempty
source tile. Considering only the b=0 mode per tile, and the
source's **computed toy precision** `p_t=1184`:

| Candidate enumeration | Admissible tuples |
| --- | ---: |
| Treat all 8 tile modes as weight 1 | 98,071,305,243,152,509,620 |
| Drop 7 provably zero mode forms | 1,184 |

These are combinatorial counts for one illustrative packet and one b,
not observed child-network creation, not a complete valid active
theorem call, and **not proof that the original implementation actually
enumerates empty tiles**. It is a precisely testable place to avoid
wasted work if it does.

## Verification

The six tests cover:

1. a single occupied source column forcing the coarse valuation;
2. all occupancy subsets of small packet grids;
3. sparse, dense, and negative Hermite-point cases;
4. equal-symbol and empty-tile cases;
5. duplicate/out-of-range/invalid evidence refusal;
6. exact source-vs-pruned modular sums for small precisions, plus
   checked original and pruned candidate counts at p=1184.

Locally restored Rust 1.99.1 passed formatting, all offline targets
and strict Clippy on the saved reference snapshot. Exact-head managed
CI is required separately for this GitHub commit.

## Next action

Integrate only the **uniform** `a+1-i+b` rule and provably
empty-mode filtering into an actual source packet-to-child evaluator,
preserving the original `b+1` enumeration as oracle. Instrument the
total live mode count, surviving multi-indices, child tensor creation,
arithmetic bit widths and actual time. Do not keep optimizing the
now-disproven per-row geometric refinement.
