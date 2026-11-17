import Mathlib

/-!
# Odd binomial coefficients for the original Cauchy grid

For the complete power-of-two grid of size N = 2^(a+1),
every binomial coefficient `(N-1).choose k` is odd. This is
the elementary factorial-parity mechanism behind the equality
of the valuations of C'(t) and C'(0) for the source grid.

The proof uses Mathlib's formally established Lucas congruence
modulo two and an induction that retains the *exact* source
power-of-two parameter. The separate derivative factorial
identity and the 2-local quotient integrality still need
formal assembly.
-/

namespace IndependentETH.CauchyBinomialParity

/-- Every coefficient in row 2^m-1 of Pascal's triangle is odd. -/
theorem choose_two_pow_sub_one_mod_two (m : ℕ) :
    ∀ k : ℕ, k < 2 ^ m →
      ((2 ^ m - 1).choose k) % 2 = 1 := by
  induction m with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by
        simp only [pow_zero] at hk
        omega
      subst k
      norm_num
  | succ m ih =>
      intro k hk
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by
        rw [pow_succ]
        ring
      have hpos : 0 < 2 ^ m := by positivity
      have hsmall : k / 2 < 2 ^ m := by omega
      have hmodn : (2 ^ (m + 1) - 1) % 2 = 1 := by omega
      have hdivn : (2 ^ (m + 1) - 1) / 2 = 2 ^ m - 1 := by omega
      have hmodk : k % 2 = 0 ∨ k % 2 = 1 := by omega
      have hchoose : (1 : ℕ).choose (k % 2) = 1 := by
        rcases hmodk with h | h <;> simp [h]
      have hLucas :=
        Choose.choose_modEq_choose_mod_mul_choose_div_nat
          (n := 2 ^ (m + 1) - 1) (k := k) (p := 2)
      have hcongr :
          ((2 ^ (m + 1) - 1).choose k) % 2 =
            (((2 ^ (m + 1) - 1) % 2).choose (k % 2) *
              ((2 ^ (m + 1) - 1) / 2).choose (k / 2)) % 2 := hLucas
      simpa [hmodn, hdivn, hchoose, ih (k / 2) hsmall] using hcongr

#print axioms IndependentETH.CauchyBinomialParity.choose_two_pow_sub_one_mod_two

end IndependentETH.CauchyBinomialParity
