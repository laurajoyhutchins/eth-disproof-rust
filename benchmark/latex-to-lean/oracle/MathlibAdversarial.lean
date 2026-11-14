import Mathlib

/- Independent adversarial mathematical oracles. Not tool output. -/
namespace LatexLeanAdversarial

theorem e03 (x : ℝ) : 0 ≤ x ^ 2 := sq_nonneg x

theorem e07 : ∀ n : ℕ, ∃ m : ℕ, n < m := by
  intro n
  exact ⟨n + 1, Nat.lt_succ_self n⟩

-- Lean totalizes inverse at zero; preserve that semantic distinction.
theorem x02_false_under_totalization : ¬ (∀ x : ℝ, (1 / x) * x = 1) := by
  intro h
  have hz := h 0
  norm_num at hz

theorem x03_false : ¬ (∃ M : ℕ, ∀ n : ℕ, n < M) := by
  rintro ⟨M, h⟩
  exact (lt_irrefl M) (h M)

theorem x04_false : ¬ (∀ x : ℝ, Real.sqrt (x ^ 2) = x) := by
  intro h
  have hx := h (-1)
  have hs : (0 : ℝ) ≤ Real.sqrt (((-1 : ℝ) ^ 2)) := Real.sqrt_nonneg _
  linarith

theorem x05_false : ¬ (∀ x y : ℝ, x ^ 2 = y ^ 2 → x = y) := by
  intro h
  have hs : (-1 : ℝ) ^ 2 = (1 : ℝ) ^ 2 := by norm_num
  have he := h (-1) 1 hs
  norm_num at he

theorem x06_vacuous : ∀ x : ℝ, (0 < x ∧ x < 0) → x = 7 := by
  intro x h
  linarith [h.1, h.2]

theorem x06_unsatisfiable : ¬ (∃ x : ℝ, 0 < x ∧ x < 0) := by
  rintro ⟨x, h1, h2⟩
  linarith

theorem strict_vs_nonstrict_not_equivalent :
    ¬ ((∀ x : ℝ, 0 ≤ x ^ 2) ↔ (∀ x : ℝ, 0 < x ^ 2)) := by
  intro h
  have wrong := h.mp (fun x => e03 x)
  have falsehood : ¬ (∀ x : ℝ, 0 < x ^ 2) := by
    intro h'
    have hz := h' 0
    norm_num at hz
  exact falsehood wrong

theorem quantifier_reversal_not_equivalent :
    ¬ ((∀ n : ℕ, ∃ M : ℕ, n < M) ↔ (∃ M : ℕ, ∀ n : ℕ, n < M)) := by
  intro h
  exact x03_false (h.mp e07)

#print axioms LatexLeanAdversarial.e03
#print axioms LatexLeanAdversarial.e07
#print axioms LatexLeanAdversarial.x02_false_under_totalization
#print axioms LatexLeanAdversarial.x03_false
#print axioms LatexLeanAdversarial.x04_false
#print axioms LatexLeanAdversarial.x05_false
#print axioms LatexLeanAdversarial.x06_vacuous
#print axioms LatexLeanAdversarial.x06_unsatisfiable
#print axioms LatexLeanAdversarial.strict_vs_nonstrict_not_equivalent
#print axioms LatexLeanAdversarial.quantifier_reversal_not_equivalent
