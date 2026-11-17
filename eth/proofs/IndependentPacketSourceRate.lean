import Mathlib

/-!
# Source packet recursion: cumulative depth-exponent budget

Original source: openai/math@4eaee87548250b2682affda7d05d947c05554bae,
preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/
build/quantitative-contraction.tex, lines 571--594.

The appendix derives the depth-d branching exponent proportional to
(s / sqrt(lambda)) * (sqrt(2) / 8)^d, using child M <= C*s*8^(-d)
and u_d = Theta_C(lambda*2^(-d)). This module proves the finite
*arithmetic summation* of that exact source decay for arbitrary depth.

It does NOT prove the packet-mode bound per node, the recursion identity,
the leaf cost, interpolation cost, or machine implementation. In
particular, this conditional rate summation is not an ETH disproof.
-/

namespace IndependentETH.PacketSourceRate

open scoped BigOperators

/-- Geometric contraction of the appendix's depth-dependent exponent. -/
noncomputable def decay : ℝ := Real.sqrt 2 / 8

theorem decay_nonneg_le_quarter :
    0 ≤ decay ∧ decay ≤ (1 / 4 : ℝ) := by
  have hroot : Real.sqrt (2 : ℝ) ≤ 2 := by
    calc
      Real.sqrt (2 : ℝ) ≤ Real.sqrt 4 :=
        Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := by norm_num
  constructor
  · unfold decay
    positivity
  · unfold decay
    nlinarith

/-- Closed finite sum for the simpler upper envelope 1/4. -/
theorem quarter_geometric_sum (depth : ℕ) :
    (∑ d ∈ Finset.range depth, (1 / 4 : ℝ) ^ d) =
      (4 / 3 : ℝ) * (1 - (1 / 4 : ℝ) ^ depth) := by
  induction depth with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem quarter_geometric_sum_bound (depth : ℕ) :
    (∑ d ∈ Finset.range depth, (1 / 4 : ℝ) ^ d) ≤ 4 / 3 := by
  rw [quarter_geometric_sum]
  have hpow : 0 ≤ (1 / 4 : ℝ) ^ depth := by positivity
  nlinarith

/--
The complete cumulative exponent of the source geometric branching
profile is at most 4A/3, for any finite recursion depth. In particular,
depth does not introduce a multiplicative logarithmic loss in the
source's main exponent, provided its per-level premise is established.
-/
theorem source_depth_exponent_bound (A : ℝ) (hA : 0 ≤ A)
    (depth : ℕ) :
    (∑ d ∈ Finset.range depth, A * decay ^ d) ≤
      (4 / 3 : ℝ) * A := by
  have hd := decay_nonneg_le_quarter
  calc
    (∑ d ∈ Finset.range depth, A * decay ^ d) ≤
        ∑ d ∈ Finset.range depth, A * (1 / 4 : ℝ) ^ d := by
      apply Finset.sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hd.1 hd.2 d) hA
    _ = A * (∑ d ∈ Finset.range depth, (1 / 4 : ℝ) ^ d) := by
      rw [Finset.mul_sum]
    _ ≤ A * (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left (quarter_geometric_sum_bound depth) hA
    _ = (4 / 3 : ℝ) * A := by ring

#print axioms IndependentETH.PacketSourceRate.decay_nonneg_le_quarter
#print axioms IndependentETH.PacketSourceRate.quarter_geometric_sum
#print axioms IndependentETH.PacketSourceRate.source_depth_exponent_bound

end IndependentETH.PacketSourceRate
