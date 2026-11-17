import Mathlib

/-!
# Exact factorial identity for a consecutive Cauchy derivative grid

For k < N, the product of every integer difference k-j, with
j running through the interval [0,N) except j=k, is exactly

  (-1)^(N-1-k) * k! * (N-1-k)!.

This file is independent of the normalization and valuation claims.
It supplies the integer-product identity to which the Lucas parity
theorem can be applied after the literal source grid is reindexed.
-/

namespace IndependentETH.CauchyFactorial

open scoped BigOperators

private theorem lower_difference_product (k : ℕ) :
    (∏ j ∈ Finset.range k, ((k : ℤ) - (j : ℤ))) =
      (k.factorial : ℤ) := by
  calc
    (∏ j ∈ Finset.range k, ((k : ℤ) - (j : ℤ))) =
        ∏ j ∈ Finset.range k, ((k - j : ℕ) : ℤ) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact (Nat.cast_sub (Nat.le_of_lt (Finset.mem_range.mp hj))).symm
    _ = (((Finset.range k).prod (fun j : ℕ => k - j) : ℕ) : ℤ) := by
      simp
    _ = (k.factorial : ℤ) := by
      rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]

private theorem upper_difference_product (k m : ℕ) :
    (∏ j ∈ Finset.Ico (k + 1) (k + 1 + m),
      ((k : ℤ) - (j : ℤ))) =
        (-1 : ℤ) ^ m * (m.factorial : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hle : k + 1 ≤ k + 1 + m := by omega
      rw [show k + 1 + (m + 1) = (k + 1 + m) + 1 by omega]
      rw [Finset.prod_Ico_succ_top hle, ih, pow_succ, Nat.factorial_succ]
      push_cast
      ring

/--
A certified exact factorial formula for the derivative product of
*any* consecutive integer grid, with no division or valuation premise.
-/
theorem integer_interval_derivative_factorial (k m : ℕ) :
    (∏ j ∈ (Finset.range (k + 1 + m)).erase k,
      ((k : ℤ) - (j : ℤ))) =
        (-1 : ℤ) ^ m * (k.factorial : ℤ) * (m.factorial : ℤ) := by
  let left : Finset ℕ := Finset.range k
  let right : Finset ℕ := Finset.Ico (k + 1) (k + 1 + m)
  have hset :
      (Finset.range (k + 1 + m)).erase k = left ∪ right := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ico, left, right]
    omega
  have hdisjoint : Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro j hj hr
    have hlt : j < k := Finset.mem_range.mp hj
    have hge : k + 1 ≤ j := (Finset.mem_Ico.mp hr).1
    omega
  rw [hset, Finset.prod_union hdisjoint]
  change
    (∏ j ∈ Finset.range k, ((k : ℤ) - (j : ℤ))) *
      (∏ j ∈ Finset.Ico (k + 1) (k + 1 + m),
        ((k : ℤ) - (j : ℤ))) =
      (-1 : ℤ) ^ m * (k.factorial : ℤ) * (m.factorial : ℤ)
  rw [lower_difference_product, upper_difference_product]
  ring

/-- The endpoint-free form for a grid of size N. -/
theorem integer_interval_derivative_factorial_at
    (N k : ℕ) (hk : k < N) :
    (∏ j ∈ (Finset.range N).erase k, ((k : ℤ) - (j : ℤ))) =
        (-1 : ℤ) ^ (N - 1 - k) *
          (k.factorial : ℤ) * ((N - 1 - k).factorial : ℤ) := by
  have hN : k + 1 + (N - 1 - k) = N := by omega
  conv_lhs => rw [← hN]
  exact integer_interval_derivative_factorial k (N - 1 - k)

#print axioms IndependentETH.CauchyFactorial.integer_interval_derivative_factorial
#print axioms IndependentETH.CauchyFactorial.integer_interval_derivative_factorial_at

end IndependentETH.CauchyFactorial
