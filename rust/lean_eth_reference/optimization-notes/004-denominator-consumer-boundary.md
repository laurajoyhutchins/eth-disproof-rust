# Optimization experiment 004: the retained denominator is an observable word

**Status:** source-grounded obstruction to claiming experiment 002 saves
end-to-end work; no executable algorithm is changed.

## What the original machine actually does

The pinned source declares:

1. [LayoutProgramPower.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramPower.lean):
   `powerCommand` writes the full little-endian `2^q` bit word.
2. [LayoutProgramIntegerCache.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramIntegerCache.lean):
   `makePower` copies the unary `R` from stack 21 to 23, removes one
   element, then calls `powerProgram` with output stack 2.
   The contract calls this explicit output `denominatorWord R`.
3. [LeafHeadSetupProgramRetain.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadSetupProgramRetain.lean):
   `retainedCopies = [(640,710),(641,711),(642,712)]`, and
   `retainCache` copies all three physically. In particular the
   denominator on stack 642 is reproduced in stack 712.
4. [SignatureHeadLoader.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoader.lean):
   the retained-cache theorem explicitly bounds the `denominatorWord`
   and preserves its length in later stages.

Thus the full word is an **observable boundary**. Its length is
`max(R-1,0)+1` bits, and existing source programs pay to copy it.
Representing only the producer as `Pow2(max(R-1,0))` cannot eliminate
the later copies without changing the subsequent machine interface.

## Consequence for the proposed improvement

The candidate `src/deferred_power.rs` still has a valid tested
standalone refinement and exact symbolic multiplication. But the first
unavoidable full-word consumer determines whether the representation
saves total work. A symbolic producer plus immediate materialization
saves **no asymptotic work**; if it allocates additional metadata, it may
even increase overhead.

This refines the earlier hypothesis; it is not evidence that the
complete optimized algorithm is faster.

## Smallest next experiment

Trace use of the retained denominator through the integer-entry
and signed coefficient operations. If all intermediate consumers admit
an exact representation-independent `Pow2` interface, define a new
explicit refinement relation and instrument materialized bits across
that entire slice. Otherwise mark the symbolic experiment as a
negative finding and do not integrate it into the canonical port.

## Source/provenance correction

Notes 001 and 002 mistakenly linked the power source under
`SqrtLogSpace`; the pinned file is actually in `SqrtLog`.
Both links are corrected by this commit. This source-level inspection
was not an imported Lean runtime verification.
