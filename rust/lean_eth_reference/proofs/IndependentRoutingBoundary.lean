import Mathlib

/-!
# Contraction routing and weighted precision: independent mathematical boundary

Sources (pinned, not imported into this deliberately small Mathlib-only module):
* Anthropic formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5,
  eth/proof/networks/Value/Sums.lean: Value.stSumsInside
  (the sum of independent group settings is a product of group sums).
* OpenAI math@4eaee87548250b2682affda7d05d947c05554bae,
  lean/OAI/Algorithms/SubexponentialSAT/SubexpComputedWeights.lean:
  SubexpComputedWeights.momentWeight_reconstruct and enumeration_weight_split
  (disjoint supports and reconstructed field assignments split monomial weights).

These sources use different network objects. These lemmas specify the common
mathematical interface. They do not assert that either pinned network has
been converted to the other's representation. In particular, OpenAI's
SubexpComputedWeights works in a prime-field construction; it must not be
conflated with the separate two-adic appendix.

A source-specific bridge must additionally exhibit:
  (1) a bijection between the original states and the routed states;
  (2) preservation of every source factor, with normalization and signs;
  (3) a valuation witness for coefficients that are truncated.
-/

namespace IndependentETH

open scoped BigOperators

/--
Independent settings of finitely many groups yield a product of group sums.

This is the exact mathematical shape of Anthropic's "sums inside the
tables", without a claim that its source network is OpenAI's packet network.
-/
theorem group_sum_product
    {G : Type*} [Fintype G] [DecidableEq G]
    {X : G → Type*} [∀ g, Fintype (X g)]
    {R : Type*} [CommSemiring R]
    (entry : (g : G) → X g → R) :
    (∑ settings ∈ Fintype.piFinset (fun g => (Finset.univ : Finset (X g))),
      ∏ g, entry g (settings g)) =
      ∏ g, ∑ setting : X g, entry g setting := by
  classical
  rw [Finset.prod_univ_sum]

/--
An outer/shared assignment cannot be moved across the product. Once fixed,
its group-local settings can be summed independently. This permits arbitrary
coupling through the outer assignment.
-/
theorem conditional_group_contraction
    {O G : Type*} [Fintype O] [Fintype G] [DecidableEq G]
    {X : G → Type*} [∀ g, Fintype (X g)]
    {R : Type*} [CommSemiring R]
    (outer : O → R) (entry : O → (g : G) → X g → R) :
    (∑ o : O, outer o *
      (∑ settings ∈ Fintype.piFinset (fun g => (Finset.univ : Finset (X g))),
        ∏ g, entry o g (settings g))) =
    ∑ o : O, outer o * (∏ g, ∑ setting : X g, entry o g setting) := by
  classical
  apply Finset.sum_congr rfl
  intro o _
  rw [group_sum_product]

/-- The only algebra needed to discard a term at precision p. -/
theorem two_power_vanishes_above_precision
    {R : Type*} [Semiring R]
    (p weight : ℕ) (hmod : (2 : R) ^ p = 0) (hw : p ≤ weight) :
    (2 : R) ^ weight = 0 := by
  calc
    (2 : R) ^ weight = (2 : R) ^ (p + (weight - p)) := by
      rw [Nat.add_sub_of_le hw]
    _ = (2 : R) ^ p * (2 : R) ^ (weight - p) := by
      rw [pow_add]
    _ = 0 := by rw [hmod, zero_mul]

/--
A Hamming-weight or degree cutoff is sound only when its coefficient contains
at least that many factors of two in the actual coefficient ring. Replacing
the exponent with an unproved "number of singlets" would be invalid.

The result works at every precision, including zero, and requires no division.
-/
theorem weighted_mode_cutoff
    {M R : Type*} [CommSemiring R]
    (modes : Finset M) (p : ℕ) (weight : M → ℕ) (amplitude : M → R)
    (hmod : (2 : R) ^ p = 0) :
    (∑ mode ∈ modes, (2 : R) ^ (weight mode) * amplitude mode) =
    ∑ mode ∈ modes.filter (fun mode => weight mode < p),
      (2 : R) ^ (weight mode) * amplitude mode := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mode _
  by_cases h : weight mode < p
  · simp [h]
  · have hv : (2 : R) ^ (weight mode) = 0 :=
      two_power_vanishes_above_precision p (weight mode) hmod (Nat.le_of_not_gt h)
    simp [h, hv]

/-- The integer signed singlet entry -1 is odd and cannot be cut at p=1. -/
theorem raw_singlet_weight_does_not_imply_valuation :
    ¬ (2 : ℤ) ∣ (-1 : ℤ) := by
  norm_num

/-- Coupled groups do not factor after summing out their common outer index. -/
theorem outer_coupling_counterexample :
    (∑ o : Fin 2, ((o.val : ℤ) + 1) * ((o.val : ℤ) + 1)) ≠
    (∑ o : Fin 2, ((o.val : ℤ) + 1)) *
      (∑ o : Fin 2, ((o.val : ℤ) + 1)) := by
  decide

#print axioms IndependentETH.group_sum_product
#print axioms IndependentETH.conditional_group_contraction
#print axioms IndependentETH.two_power_vanishes_above_precision
#print axioms IndependentETH.weighted_mode_cutoff
#print axioms IndependentETH.raw_singlet_weight_does_not_imply_valuation
#print axioms IndependentETH.outer_coupling_counterexample

end IndependentETH
