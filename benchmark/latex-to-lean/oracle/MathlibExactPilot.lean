import Mathlib

namespace LatexLeanPilot

-- Independent oracle statements: never provided to the candidate formalizer.
theorem e01 (a b : ℝ) : a + b = b + a := by
  exact add_comm a b

def swap (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1)

theorem r01 (p : ℝ × ℝ) : swap (swap p) = p := by
  cases p
  rfl

-- Explicitly quantify the recurrence and its base case.
theorem g01 (F : ℕ → ℕ)
    (h0 : F 0 = 1)
    (hs : ∀ n : ℕ, F (n + 1) = (n + 1) * F n) :
    ∀ n : ℕ, F n = Nat.factorial n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    calc
      F (n + 1) = (n + 1) * F n := hs n
      _ = (n + 1) * Nat.factorial n := by rw [ih]
      _ = Nat.factorial (n + 1) := by simp [Nat.factorial_succ, Nat.mul_comm]

-- The original X01 statement is false over REAL numbers, with x = 0.
theorem x01_false : ¬ (∀ x : ℝ, 0 < x ^ 2) := by
  intro h
  have hzero := h 0
  norm_num at hzero

#print axioms LatexLeanPilot.e01
#print axioms LatexLeanPilot.r01
#print axioms LatexLeanPilot.g01
#print axioms LatexLeanPilot.x01_false
