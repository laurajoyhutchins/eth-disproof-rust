# Paper theorem interface versus generalized Sudoku

**Status:** a quantitative family-level parameter correction and finite,
reproducible structural probes. This does **not** prove non-refusal, total
bit-complexity, or a subexponential bound in the number of Sudoku cells.

Primary source: OpenAI, *The Exponential Time Hypothesis is False*, October
25, 2026 revision, Appendix D (the Boolean tensor contraction theorem,
"Parameters and collision packing", and "The child networks and their
descriptions"):
[quantitative-reduction.tex](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex),
[quantitative-contraction.tex](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex).

## 1. Choose the correct growing size parameter

Let a Sudoku box order be `b`, its side `n=b^2`, and its cell count
`N=n^2`. In the existing **direct bipartite Boolean network** (not the
separate 3-CNF encoding), put `t=ceil(log2(n))`, at least one bit. Exact
network dimensions are:

- `M=3Nt` edges;
- `V=N+3n` vertices;
- `deg_max=max(n,3)*t`;
- `P0=Nt+1` counting precision, sufficient to prevent modular wraparound.

The tensor theorem assumes `M<=Cs` for a *single constant* `C` for all
sizes of the family, with at most polynomially many vertices, bounded
degree `Delta=ceil(s^(9/10))`, polynomial-length descriptions, and
uniformly bounded-cost local entry oracles. The earlier counterexample
used `s=V`, but **`s=V` is not a valid uniform size choice** for this
direct Sudoku family. Indeed,

    M/V = 3nt/(n+3) = Theta(log N).

To see the unbounded ratio with integers, choose `b=2^k`, whence
`n=2^(2k)`, `t=2k` and `M/V=6kn/(n+3)>3k` for `k>=1`.
No fixed `C` suffices.

**Use `s=M`** (or `max(2,M)` for the singleton edge case). Then `M<=s`
with `C=1`, `V<=4M/3` for all `n>=1`, and `P0<=M`. For `n>=4` the
maximum degree is `nt`. Since `t<=n`, we have

    (nt)^10 <= (3 n^2 t)^9   <=>   t <= 3^9 n^8,

so `nt<=s^(9/10)<=Delta`. The finitely many smaller cases satisfy the
ceiling inequality directly. Local Sudoku cell and unit oracles have
polynomial-time Boolean evaluation, and their input descriptions have
polynomial length in `M`. This establishes the **input-side numerical and
uniformity hypotheses** for the direct reduction with `s=M`.

### The missing cell-based bound

The theorem's advertised time is, suppressing polynomial factors,

    2^{O(s/sqrt(log s))}.

For this direct encoding `s=M=Theta(N log N)`, giving only

    2^{O(N sqrt(log N))}.

This upper bound is `2^{o(M)}` but is **not a certificate of `2^{o(N)}`**
when `N` is the number of Sudoku cells. It could still beat brute-force
`n^N=2^{Theta(N log N)}` in the certified asymptotic model. It does not
establish the stronger desired cell-count theorem. A better reduction,
a stronger contraction bound, or a different complexity parameter would
be required. An upper bound that is not `2^{o(N)}` does not establish a
lower bound on the solver's actual running time.

## 2. Literal paper schedule is inactive at all constructible Sudoku sizes

At the root `lambda=(s-1).bit_length()` and
`u_0=floor(lambda/131072)`. When `lambda<131072` the implementation
branches directly to its leaf, without packing. The first potentially
active value is `s=2^131071+1` (`lambda=131072`), with `r=64`, `a=2`,
`u=1`. Even then `M>H`, the numerical packing inequalities, bounded
mode expansion, and every relevant capacity budget must be checked.
The published theorem permits a **fixed finite range** of smaller sizes
to be handled by direct summation; this implementation's 18-edge default
leaf cap does not execute that unbounded finite-range promise.

For `b>=2` with `lambda<131072`, the direct Sudoku network already has
at least 96 edges and therefore refuses the default paper leaf. The
existing 4x4 input is an executable example. The regression test
`test_real_4x4_literal_paper_still_refuses_with_corrected_s` constructs a
real engine at `s=M=96`, `p=33` and observes the same refusal. Setting
`s=M` repairs the
asymptotic size interface but does not repair that non-refusal issue.

## 3. Inspect actual packings and *constructed* children

Run `PYTHONPATH=src:. python scripts/admissibility_audit.py` to generate a
machine-readable record. It constructs the real blank Sudoku networks,
**counterfactually forces** `r=64,a=2`, audits packet and group loads,
catalogues modes at precision 3, and materializes the maximum-load child
with all mode multiplicities zero. The child's graph is independent of
these multiplicities; its exact coefficient values are not.

| Board | Edges | Packets | Packet slots | Max child edges | Child vertices | Modes |
|---|---:|---:|---:|---:|---:|---:|
| 4x4 | 96 | 84 | 336 | 14 | 86 | 138 |
| 9x9 | 972 | 903 | 3,612 | 60 | 906 | 1,568 |
| 16x16 | 3,072 | 2,880 | 11,520 | 112 | 2,885 | 4,536 |

Every inspected network satisfies exact port conservation and packet
orientation; each materialized child validates its bipartite incidence.
The 9x9 and 16x16 counterfactual child load distributions already meet
`32*M_child<=3*M_parent` and `max_degree_child<=Delta`. The 4x4 load
bound does not.

All three cases fail `packet_count*L<=3M`, and **none satisfies the
paper's required huge input-side numerical packing preconditions**:

    M >= 2 (r^(2a))^2 Delta,
    M >= L r^(2a),
    2L <= Delta.

Thus these measurements do **not** contradict the packing lemma. They
instead show which invariants cannot be invoked outside its hypotheses.
A finite case also cannot certify the lemma for all large inputs.

The 16x16 forced packing produces 4,536 modes even at precision 3,
exceeding the implementation's default `ModeConfig.max_modes=2000`.
This is a concrete budget mismatch for the **probe**, not a claim that the
inactive literal paper schedule actually executed mode construction.

## 4. Conditional structural preservation is not the missing proof

Suppose at an active call the paper's packing lemma succeeds with
`P<=3M/L` packets, group-side load `<=3M/r`, and `2L<=Delta`. Then:

- Every group child has at most `6M/r=3M/32` edges, regardless of `beta`.
- Its retained original vertices have degree at most `Delta`.
- Its new packet vertices have at most `2L<=Delta` ports.
- Its vertex count is at most `V+P<=V+M` because paper-active `a>=2`
  entails `L>=4`.

These facts prove **conditional preservation of the graph-side degree,
edge shrinkage, and polynomial vertex-count bounds**. The source paper
has analogous arguments. This is not the same as proving that the
current `balanced_labels` implementation always finds a valid packing
under the lemma's numerical hypotheses, nor that all recursively
created packet-entry oracles satisfy the necessary *uniform bit-cost*
bounds and creation-precision semantics.

The runtime does check active paper packings and live child size/degree
and raises if invariants are broken. That fail-closed policy is not a
non-refusal proof.

## 5. What still blocks completion

1. **Uniform packing implementation.** Prove that `balanced_labels` and
   `pack` implement the conditional-expectation construction under the
   numerical hypotheses, including padded-label classes and the packet
   bound. Tiny tests outside the hypotheses are insufficient.
2. **Entry-oracle closure.** Prove that the actual `PacketEntry` across
   repeated recursive generations has descriptions of polynomial total
   length, proper creation-time 2-adic representatives, and uniformly
   bounded bit cost under all supported modes and rings.
3. **Resource budgets.** The finite mode, factor, memory, and child limits
   must either be shown sufficient for every member of a growing family,
   or the algorithm must be defined with justified size-dependent bounds.
4. **Successful leaf policy.** The fixed leaf cap does not implement the
   theorem's finite-size base-case argument. The independent exhaustive
   fallback is not silently selected, and making that fallthrough explicit
   does not make the workload practical.
5. **Total bit-cost and cell-size claim.** Complete the local recurrence
   and distinguish a `2^{o(M)}` Boolean-network theorem from `2^{o(N)}`
   cell-based generalized Sudoku solving.

No item here constitutes a new ETH refutation or disproof of the
underlying tensor contraction theorem. It is an audit of what this
specific repository actually implements and what follows from its input
encoding.
