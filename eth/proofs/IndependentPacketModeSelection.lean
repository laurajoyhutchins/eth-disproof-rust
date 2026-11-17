import Mathlib

/-!
# Weighted Cauchy-mode selections: finite algebraic cutoff

Original packet source:
openai/math@4eaee87548250b2682affda7d05d947c05554bae,
`quantitative-contraction.tex`, equations
`tensor-mode-expansion`, `tensor-mode-budget`, and `tensor-recursion-identity`.

Each row factor `l₀(z)=1-z` or `l₁(z)=z` is affine in the
crossing modes. A fully distributed term therefore chooses either
its constant term or one mode from each row. The source's missing
valuation bridge must establish that the coefficient of a mode
of weight `w` is exactly `2^w` times an element of the
*actual* coefficient ring `A_p`.

Once that source-specific factorization is supplied, the finite
product lemma below proves that a distributed term contains the
power `2^(sum of selected weights)`. The cutoff discards all
terms with total weight at least the modulus precision.

This module does NOT prove the Cauchy valuation, the equality of
distributed and grouped mode coefficients, the group-child
contraction identity, or the per-node cost bound. No assertion
that the original source packets have already been verified is
made here.
-/

namespace IndependentETH.PacketModeSelection

open scoped BigOperators

/-- The weight contributed by one row's affine-factor choice. -/
def rowWeight {Row Mode : Type*}
    (weight : Mode → ℕ) (pick : Row → Option Mode) (row : Row) : ℕ :=
  match pick row with
  | none => 0
  | some mode => weight mode

/-- Select the constant term or a crossing-mode term with its power of two. -/
def chosenFactor {Row Mode R : Type*} [CommSemiring R]
    (weight : Mode → ℕ) (constant : Row → R)
    (amplitude : Row → Mode → R)
    (pick : Row → Option Mode) (row : Row) : R :=
  match pick row with
  | none => constant row
  | some mode => (2 : R) ^ (weight mode) * amplitude row mode

/-- The remaining factor after removing the required power of two. -/
def strippedFactor {Row Mode R : Type*} [CommSemiring R]
    (constant : Row → R) (amplitude : Row → Mode → R)
    (pick : Row → Option Mode) (row : Row) : R :=
  match pick row with
  | none => constant row
  | some mode => amplitude row mode

/--
Every finite distributed row-product contains the product of its
selected powers of two. This is algebraic, independent of the
number of rows, modes, or the signs absorbed into amplitudes.
-/
theorem chosen_product_has_weight
    {Row Mode R : Type*} [Fintype Row] [CommSemiring R]
    (weight : Mode → ℕ) (constant : Row → R)
    (amplitude : Row → Mode → R) (pick : Row → Option Mode) :
    (∏ row : Row, chosenFactor weight constant amplitude pick row) =
      (2 : R) ^ (∑ row : Row, rowWeight weight pick row) *
        (∏ row : Row, strippedFactor constant amplitude pick row) := by
  classical
  have hrow (row : Row) :
      chosenFactor weight constant amplitude pick row =
        (2 : R) ^ (rowWeight weight pick row) *
          strippedFactor constant amplitude pick row := by
    cases h : pick row with
    | none => simp [chosenFactor, strippedFactor, rowWeight, h]
    | some mode => simp [chosenFactor, strippedFactor, rowWeight, h]
  calc
    (∏ row : Row, chosenFactor weight constant amplitude pick row) =
        ∏ row : Row, ((2 : R) ^ (rowWeight weight pick row)) *
          strippedFactor constant amplitude pick row := by
      apply Finset.prod_congr rfl
      intro row _
      exact hrow row
    _ = (∏ row : Row, (2 : R) ^ (rowWeight weight pick row)) *
          (∏ row : Row, strippedFactor constant amplitude pick row) := by
      rw [Finset.prod_mul_distrib]
    _ = (2 : R) ^ (∑ row : Row, rowWeight weight pick row) *
          (∏ row : Row, strippedFactor constant amplitude pick row) := by
      rw [← Finset.prod_pow_eq_pow_sum]

/--
The source's weighted precision cutoff, proved at the level of
*actual affine-row selections* rather than postulating that an
already-grouped coefficient is divisible by its weight.

To instantiate with the original packet, `amplitude` must come
from a proved Cauchy-mode coefficient factorization in `A_p`.
-/
theorem precision_discards_heavy_selections
    {Row Mode R : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Mode] [DecidableEq Mode] [CommSemiring R]
    (weight : Mode → ℕ) (constant : Row → R)
    (amplitude : Row → Mode → R)
    (p : ℕ) (hmod : (2 : R) ^ p = 0) :
    (∑ pick : Row → Option Mode,
      ∏ row : Row, chosenFactor weight constant amplitude pick row) =
    ∑ pick ∈ (Finset.univ : Finset (Row → Option Mode)).filter
        (fun pick => (∑ row : Row, rowWeight weight pick row) < p),
      ∏ row : Row, chosenFactor weight constant amplitude pick row := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro pick _
  by_cases h : (∑ row : Row, rowWeight weight pick row) < p
  · simp [h]
  · have hw : p ≤ ∑ row : Row, rowWeight weight pick row :=
      Nat.le_of_not_gt h
    have hzero : (2 : R) ^ (∑ row : Row, rowWeight weight pick row) = 0 := by
      calc
        (2 : R) ^ (∑ row : Row, rowWeight weight pick row) =
            (2 : R) ^ (p + ((∑ row : Row, rowWeight weight pick row) - p)) := by
          rw [Nat.add_sub_of_le hw]
        _ = (2 : R) ^ p *
              (2 : R) ^ ((∑ row : Row, rowWeight weight pick row) - p) := by
          rw [pow_add]
        _ = 0 := by rw [hmod, zero_mul]
    rw [chosen_product_has_weight weight constant amplitude pick]
    simp [h, hzero]

/-- Number of row factors that select a particular crossing mode. -/
def selectedMultiplicity {Row Mode : Type*}
    [Fintype Row] [DecidableEq Row] [DecidableEq Mode]
    (pick : Row → Option Mode) (mode : Mode) : ℕ :=
  ((Finset.univ : Finset Row).filter (fun row => pick row = some mode)).card

/--
A distributed term's sum of selected row weights is the weighted
degree of its mode monomial. This identifies the precision cutoff
with the original appendix's mode-exponent budget.
-/
theorem selection_weight_eq_mode_degree
    {Row Mode : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Mode] [DecidableEq Mode]
    (weight : Mode → ℕ) (pick : Row → Option Mode) :
    (∑ row : Row, rowWeight weight pick row) =
      ∑ mode : Mode, weight mode * selectedMultiplicity pick mode := by
  classical
  have hrow (row : Row) :
      rowWeight weight pick row =
        ∑ mode : Mode,
          if pick row = some mode then weight mode else 0 := by
    cases h : pick row with
    | none => simp [rowWeight, h]
    | some mode => simp [rowWeight, h]
  calc
    (∑ row : Row, rowWeight weight pick row) =
        ∑ row : Row, ∑ mode : Mode,
          if pick row = some mode then weight mode else 0 := by
      apply Finset.sum_congr rfl
      intro row _
      exact hrow row
    _ = ∑ mode : Mode, ∑ row : Row,
          if pick row = some mode then weight mode else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ mode : Mode, weight mode * selectedMultiplicity pick mode := by
      apply Finset.sum_congr rfl
      intro mode _
      calc
        (∑ row : Row, if pick row = some mode then weight mode else 0) =
            ∑ row ∈ (Finset.univ : Finset Row).filter
              (fun row => pick row = some mode), weight mode := by
          rw [Finset.sum_filter]
        _ = weight mode * selectedMultiplicity pick mode := by
          simp [selectedMultiplicity, mul_comm]

/--
For a *fixed mode-exponent tuple*, the sum of all distributed
affine-row selections with precisely those exponents contains the
power of two dictated by the weighted degree. This is stronger than
discarding individual heavy selections: it proves divisibility of
the grouped coefficient itself.

To identify this sum with the original Cauchy packet's polynomial
coefficient still requires its source-specific affine expansion
and valuation witness, which are not postulated as theorems here.
-/
theorem grouped_coefficient_has_weight
    {Row Mode R : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Mode] [DecidableEq Mode] [CommSemiring R]
    (weight : Mode → ℕ) (constant : Row → R)
    (amplitude : Row → Mode → R) (beta : Mode → ℕ) :
    (∑ pick ∈ (Finset.univ : Finset (Row → Option Mode)).filter
        (fun pick => ∀ mode, selectedMultiplicity pick mode = beta mode),
      ∏ row : Row, chosenFactor weight constant amplitude pick row) =
      (2 : R) ^ (∑ mode : Mode, weight mode * beta mode) *
        (∑ pick ∈ (Finset.univ : Finset (Row → Option Mode)).filter
            (fun pick => ∀ mode, selectedMultiplicity pick mode = beta mode),
          ∏ row : Row, strippedFactor constant amplitude pick row) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pick hp
  have hbeta : ∀ mode, selectedMultiplicity pick mode = beta mode :=
    (Finset.mem_filter.mp hp).2
  have hweight :
      (∑ row : Row, rowWeight weight pick row) =
        ∑ mode : Mode, weight mode * beta mode := by
    rw [selection_weight_eq_mode_degree]
    apply Finset.sum_congr rfl
    intro mode _
    rw [hbeta mode]
  rw [chosen_product_has_weight, hweight]

#print axioms IndependentETH.PacketModeSelection.chosen_product_has_weight
#print axioms IndependentETH.PacketModeSelection.selection_weight_eq_mode_degree
#print axioms IndependentETH.PacketModeSelection.grouped_coefficient_has_weight
#print axioms IndependentETH.PacketModeSelection.precision_discards_heavy_selections

end IndependentETH.PacketModeSelection
