import Mathlib
import IndependentCauchySourceGrid

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

/--
The factorial identity now applies to the *literal original* Cauchy
derivative product. There is no abstract replacement of the source
grid or assumption about its factors.
-/
theorem source_derivative_factorial
    (a : ℕ) (t : ℤ)
    (ht : t ∈ IndependentETH.CauchySourceGrid.sourceGrid a) :
    IndependentETH.CauchySourceGrid.sourceDerivativeAt a t =
      (-1 : ℤ) ^ (2 ^ (a + 1) - 1 -
        IndependentETH.CauchySourceGrid.gridIndex a t) *
      ((IndependentETH.CauchySourceGrid.gridIndex a t).factorial : ℤ) *
      ((2 ^ (a + 1) - 1 -
        IndependentETH.CauchySourceGrid.gridIndex a t).factorial : ℤ) := by
  rw [IndependentETH.CauchySourceGrid.source_derivative_reindexed a t ht]
  exact integer_interval_derivative_factorial_at
    (2 ^ (a + 1))
    (IndependentETH.CauchySourceGrid.gridIndex a t)
    (IndependentETH.CauchySourceGrid.gridIndex_lt a t ht)

/--
The source derivative, multiplied by its indexed binomial
coefficient, has the uniform signed factorial numerator.
This is an exact identity over integers, not a cancellation in
a quotient where the derivative may be a nonunit.
-/
theorem source_derivative_mul_choose
    (a : ℕ) (t : ℤ)
    (ht : t ∈ IndependentETH.CauchySourceGrid.sourceGrid a) :
    IndependentETH.CauchySourceGrid.sourceDerivativeAt a t *
      (((2 ^ (a + 1) - 1).choose
        (IndependentETH.CauchySourceGrid.gridIndex a t) : ℕ) : ℤ) =
      (-1 : ℤ) ^ (2 ^ (a + 1) - 1 -
        IndependentETH.CauchySourceGrid.gridIndex a t) *
      (((2 ^ (a + 1) - 1).factorial : ℕ) : ℤ) := by
  let n : ℕ := 2 ^ (a + 1) - 1
  let k : ℕ := IndependentETH.CauchySourceGrid.gridIndex a t
  have hkn : k ≤ n := by
    have hlt := IndependentETH.CauchySourceGrid.gridIndex_lt a t ht
    dsimp [n, k]
    omega
  have hchoose := Nat.choose_mul_factorial_mul_factorial hkn
  change IndependentETH.CauchySourceGrid.sourceDerivativeAt a t *
    (n.choose k : ℤ) = (-1 : ℤ) ^ (n - k) * (n.factorial : ℤ)
  rw [source_derivative_factorial a t ht]
  change ((-1 : ℤ) ^ (n - k) * (k.factorial : ℤ) *
      ((n - k).factorial : ℤ)) * (n.choose k : ℤ) =
        (-1 : ℤ) ^ (n - k) * (n.factorial : ℤ)
  calc
    ((-1 : ℤ) ^ (n - k) * (k.factorial : ℤ) *
        ((n - k).factorial : ℤ)) * (n.choose k : ℤ) =
      (-1 : ℤ) ^ (n - k) *
        ((n.choose k * k.factorial * (n - k).factorial : ℕ) : ℤ) := by
        push_cast
        ring
    _ = (-1 : ℤ) ^ (n - k) * (n.factorial : ℤ) := by
      rw [hchoose]

#print axioms IndependentETH.CauchyFactorial.integer_interval_derivative_factorial
#print axioms IndependentETH.CauchyFactorial.integer_interval_derivative_factorial_at
#print axioms IndependentETH.CauchyFactorial.source_derivative_factorial
#print axioms IndependentETH.CauchyFactorial.source_derivative_mul_choose

end IndependentETH.CauchyFactorial
