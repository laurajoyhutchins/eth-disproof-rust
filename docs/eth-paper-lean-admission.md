# Paper/Lean admission: explicit mathematical family, not a giant execution

**Scope.** This is a source-pinned bridge between the October 25, 2026
manuscript and the accompanying Lean theorem. It does **not** prove
the original algorithm's bit-complexity claims independently, execute
an astronomically large CNF, or execute the Lean primitive machine.

## Pinned original sources

Both sources are from `openai/math` revision
[`4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae).

| Source | Exact reference | Role |
| --- | --- | --- |
| [Manuscript: The Exponential Time Hypothesis is False](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex) | Main theorem; Step 5, equation `overview-explicit-parameters`; Lemma `incidence-labels` | The explicit parameter schedule and incidence inequalities |
| [Lean endpoint](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean) | `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_eth`; `compiled_exact_count_and_sat` | An existence theorem for a compiled primitive `BitProgram.Program 80 1220` with exact count, time and visited-space properties |
| [Lean scope note](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/378.md) | `lean/docs/378.md` | States Lean's weaker `(log log n)^2` exponent versus the sharper manuscript `log log n` exponent |

**These are different interfaces.** The Python implementation's
`construct_paper_bounded_designs` is a bounded research
translation of the manuscript's spectral construction. The Lean
endpoint proves a fixed-width exact-counting statement for a
primitive program. This work neither identifies a particular
Python execution with that Lean program nor checks a new Lean
theorem. The Lean theorem is used as an upstream specification,
not as a machine-execution oracle.

## A family satisfying the full Step-5 sufficient inequalities

For `L=2**34=17,179,869,184`, define the symbolic CNF

```
n = 2**L
F_n = AND_{i=1}^n x_i
M = n, b = 1, w = 1, #F_n = 1
```

It has width at most two, so it lies within the input width
of Lean's `exact_count_eth` theorem for fixed `k=2`.
The source's `n>=20` condition also holds.

The manuscript's *literal Step-5 integers* are

```
lambda = L
nu = ceil(log2 lambda) = 34
r = floor(sqrt(lambda)/nu**2) = 113
Q = floor(lambda/(128*nu)) = 3,947,580
R = 4*ceil(sqrt(lambda)) = 524,288
D = r**(2Q) = 113**7,895,160
tau = 1/(r*lambda)
```

In particular:

| Paper condition | Exact finite arithmetic / certificate |
| --- | --- |
| `6R <= Q` | `3,145,728 <= 3,947,580` |
| `R >= 32` | `524,288 >= 32` |
| `R**2 >= 2048Qnu` | `274,877,906,944 >= 274,877,890,560` |
| `2(b+w)D**2 <= M` | Proved by an integer-bit upper bound on D, with b=w=1, M=n |
| Stronger overview `12D**2 <= M` | Proved by the same conservative bound |
| `2Qr**2 <= n` | Exact integer bit-length comparison with n=2**L |
| `D**128 <= 2n` | Proved from `D < 2**(2Q*bit_length(r))` |
| `2q <= n` where `q=floor(3nR/Q)` | Follows from `6R <= Q` |
| `Q(q+1) > 3nR` | Exact floor identity for Hermite uniqueness |

Here `bit_length(r)=7`, giving

```
D < 2**55,266,120,
D**128 < 2**7,074,063,360 < 2**(L+1) = 2n.
```

All comparisons are *certified sufficient inequalities* using
small integers in `paper_admitted_witness.virtual_unit_cnf_step5`.
The entire virtual object is a mathematical family descriptor.
It never computes `2**L`, `D`, a size-n clause list,
an exact deformation polynomial, or a Lean machine trace.

The binary integer `n=2**L` itself would occupy at least
`L+1=17,179,869,185` bits (roughly 2 GiB), even before
constructing the actual CNF. Satisfying the asymptotic assumptions
is **not** the same as demonstrating feasible machine execution.

The original `parameters.derive_paper_parameters` implementation
is tested against the symbolic derivation at a smaller, representable
`L=2**20` to prevent a parallel formula from silently drifting.

## A *physically realized* incidence-balancing lemma witness

The paper's Lemma `incidence-labels` makes the hypotheses

```
n <= M <= b*n
2*(b+w)*D**2 <= M
2*Q*r**2 <= n
D = r**(2Q).
```

We can genuinely satisfy **this lemma** at `n=4096` on the
same independent-positive-unit-clause family with `r=Q=2`,
`D=16`, `b=w=1`, and `M=n`:

```
2*(b+w)*D**2 = 1024 <= M=4096
12*D**2 = 3072 <= M=4096   # stronger overview requirement
2*Q*r**2 = 16 <= n=4096
```

Define each variable schedule `a_v` using the bottom two bits
of zero-based `v`, and each clause schedule `d_e` using the
next two bits of `e=v`. This distributes the 4096 incidences
exactly among the 16 labels, each with load 256.
The maximum group size is 2048, and the paper's conclusions are

```
max_label_load = 256 <= 2M/D = 512
max_group_size = 2048 <= 2n/r = 4096.
```

`concrete_unit_balance_witness` materializes and checks **every**
one of these schedules and incidences. Its zero-based labels
are merely the repository equivalent of the manuscript's
one-based `[r]` indexing.

The balance lemma is **only one component** of the original
construction. At n=4096 the paper's Step-5 parameter rule
does *not* define usable r and Q, so this finite lemma witness
is **not** a full paper-admitted execution. Conversely, the
virtual full-Step-5 witness satisfies the symbolic premises but
does **not** execute the lemma's constructive algorithm.

## What we have and what remains missing

1. **Now available:** One explicitly described family for which
   the manuscript's Step-5 *sufficient inequalities* all hold,
   plus an independently verified, finite execution of the
   incidence-balancing witness.
2. **Not available:** A physically realized CNF and replacement
   system with the enormous literal Step-5 parameters, or a
   source-pinned Lean primitive trace on that CNF.
3. **Not transferred:** Any rank-2 or rank-3 observation from
   the non-admitted `r=Q=R=2` experiments. It would be invalid
   to apply those finite rank measurements to this admitted
   asymptotic family.
4. **Open mathematical obligation:** Establish small and cheaply
   constructible *intermediate* representations under admitted
   parameters, including full Taylor coefficients, rational
   coefficient bit costs and non-refusal. The final answer of
   this particular unit-clause family is trivially one, which
   says nothing about worst-case #SAT.

Lean's fixed-width theorem states a higher-level guarantee.
Our Python crosswalk checks only the manuscript parameter
arithmetic and an independent combinatorial instance. The Lean
proof and the Python spectral implementation remain **unconnected
at the program refinement level**.

## Reproduce

```bash
python -m pytest -q tests/eth/test_paper_admitted_witness.py
python -m benchmarks.eth.paper_admitted_witness \
  --lambda-bits 17179869184 --finite-n 4096 \
  --output artifacts/eth-paper-admission.json
```

The opt-in CNF scaling workflow preserves the JSON evidence,
including exact input source revisions, every passed check,
refusal boundaries and explicit `executed_lean_machine=false`.
