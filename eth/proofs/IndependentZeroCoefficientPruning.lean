import Mathlib

/-!
# Exact zero-coefficient composition and monotone support pruning

This is the mathematical boundary for the bounded Rust experiment:
only the constant coefficient of an N[t] violation polynomial is required
for #SAT. The generic polynomial identities do not depend on positivity;
the support-omission rule uses zero as an annihilator.

The statements prove the *mathematical semiring map*, not that a
particular mutable Rust table or support-index join refines it.
-/

namespace IndependentETH.ZeroCoefficient

open scoped BigOperators

/-- The constant-coefficient observable is already a ring homomorphism.
No tropical minimum-energy information is required for this observable. -/
def observe : Polynomial ℕ →+* ℕ := Polynomial.constantCoeff

theorem observe_coeff (p : Polynomial ℕ) :
    observe p = p.coeff 0 := by
  exact Polynomial.constantCoeff_apply p

theorem observe_add (p q : Polynomial ℕ) :
    observe (p + q) = observe p + observe q := map_add observe p q

theorem observe_mul (p q : Polynomial ℕ) :
    observe (p * q) = observe p * observe q := map_mul observe p q

/-- Exact elimination over a finite set commutes with reading the
constant term, even when every summand is a product of polynomials. -/
theorem observe_finite_fiber {α : Type} (s : Finset α)
    (left right : α → Polynomial ℕ) :
    observe (∑ i ∈ s, left i * right i) =
      ∑ i ∈ s, observe (left i) * observe (right i) := by
  simp only [map_sum, map_mul]

/-- A locally violated factor contributes exactly zero to #SAT;
the full polynomial may nevertheless have positive-energy terms. -/
theorem observe_energy_monomial (energy : ℕ) :
    observe (Polynomial.monomial energy (1 : ℕ)) =
      if energy = 0 then 1 else 0 := by
  simp [observe_coeff, Polynomial.coeff_monomial]

/-- A zero contribution can be omitted from a finite exact
zero-coefficient contraction without losing later solutions. -/
theorem prune_zero_fibers {α : Type} (s : Finset α)
    (left right : α → ℕ) :
    (∑ i ∈ s, left i * right i) =
      ∑ i ∈ s, if left i = 0 ∨ right i = 0 then 0 else left i * right i := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : left i = 0 ∨ right i = 0
  · rcases h with h | h
    · simp [h]
    · simp [h]
  · simp [h]

/-- No positive-energy term can create a zero-energy count through
multiplication with a nonnegative violation energy. -/
theorem positive_energy_cannot_repair (a b : ℕ) (ha : a ≠ 0) :
    observe (Polynomial.monomial a (1 : ℕ) *
      Polynomial.monomial b (1 : ℕ)) = 0 := by
  rw [observe_mul, observe_energy_monomial]
  simp [ha]

#print axioms observe_finite_fiber
#print axioms prune_zero_fibers
#print axioms positive_energy_cannot_repair

end IndependentETH.ZeroCoefficient
