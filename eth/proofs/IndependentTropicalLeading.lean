import Mathlib

/-!
# Tropical leading data and the exact CNF violation polynomial

The coefficient theorem uses the full finite polynomial as a specification.
It is independent of optimized contraction and includes unused declared
variables. The leading pair below is a partial algebraic interface;
its full semiring laws and polynomial homomorphism remain proof obligations.
-/

namespace IndependentETH.Tropical

open scoped BigOperators

abbrev Clause (n : ℕ) := List (Fin n × Bool)
abbrev CNF (n : ℕ) := List (Clause n)

/-- A literal is true when its assigned value agrees with its sign. -/
def clauseTrue {n : ℕ} (a : Fin n → Bool) (clause : Clause n) : Bool :=
  clause.any (fun lit => a lit.1 == lit.2)

/-- Exactly one unit of energy is charged per *violated clause*. -/
def energy {n : ℕ} : CNF n → (Fin n → Bool) → ℕ
  | [], _ => 0
  | clause :: rest, a =>
      (if clauseTrue a clause then 0 else 1) + energy rest a

/-- Every declared variable belongs to the enumeration, even if unused. -/
noncomputable def generating {n : ℕ} (φ : CNF n) : Polynomial ℕ :=
  ∑ a : Fin n → Bool, Polynomial.monomial (energy φ a) 1

/-- The independently defined coefficient histogram. -/
def multiplicity {n : ℕ} (φ : CNF n) (k : ℕ) : ℕ :=
  ∑ a : Fin n → Bool, if energy φ a = k then 1 else 0

/-- Every coefficient counts precisely the assignments with that energy. -/
theorem coeff_generating {n : ℕ} (φ : CNF n) (k : ℕ) :
    (generating φ).coeff k = multiplicity φ k := by
  classical
  simp [generating, multiplicity, Polynomial.coeff_monomial]

/-- Zero energy means that every clause has at least one true literal. -/
theorem energy_eq_zero_iff {n : ℕ} (φ : CNF n) (a : Fin n → Bool) :
    energy φ a = 0 ↔ ∀ clause ∈ φ, clauseTrue a clause = true := by
  induction φ with
  | nil => simp [energy]
  | cons clause rest ih =>
      simp [energy, ih, Nat.add_eq_zero_iff]

/-- The constant coefficient of the generating polynomial is exactly #SAT. -/
theorem count_satisfying {n : ℕ} (φ : CNF n) :
    (generating φ).coeff 0 =
      ∑ a : Fin n → Bool,
        if (∀ clause ∈ φ, clauseTrue a clause = true) then 1 else 0 := by
  classical
  rw [coeff_generating]
  simp only [multiplicity]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : energy φ a = 0
  · have hs := (energy_eq_zero_iff φ a).mp h
    simp [h, hs]
  · have hs : ¬ (∀ clause ∈ φ, clauseTrue a clause = true) := by
      intro hc
      exact h ((energy_eq_zero_iff φ a).mpr hc)
    simp [h, hs]

/-- The nonzero leading pair stores a degree and a strictly positive count. -/
structure Term where
  degree : ℕ
  count : ℕ
  count_pos : 0 < count

/-- `none` is the additive zero, not a finite degree with zero count. -/
abbrev Leading := Option Term

def plus : Leading → Leading → Leading
  | none, b => b
  | a, none => a
  | some a, some b =>
      if a.degree < b.degree then some a
      else if b.degree < a.degree then some b
      else some ⟨a.degree, a.count + b.count, by
        have ha := a.count_pos
        have hb := b.count_pos
        omega⟩

def times : Leading → Leading → Leading
  | none, _ => none
  | _, none => none
  | some a, some b =>
      some ⟨a.degree + b.degree, a.count * b.count,
        Nat.mul_pos a.count_pos b.count_pos⟩

def monomial (degree count : ℕ) (positive : 0 < count) : Leading :=
  some ⟨degree, count, positive⟩

theorem plus_zero (x : Leading) : plus x none = x := by
  cases x <;> rfl

theorem zero_plus (x : Leading) : plus none x = x := rfl

theorem times_zero (x : Leading) : times x none = none := by
  cases x <;> rfl

theorem zero_times (x : Leading) : times none x = none := rfl

theorem monomial_times (d e a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    times (monomial d a ha) (monomial e b hb) =
      monomial (d + e) (a * b) (Nat.mul_pos ha hb) := rfl

theorem monomial_plus_equal (d a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    plus (monomial d a ha) (monomial d b hb) =
      monomial d (a + b) (by omega) := by
  simp [plus, monomial]

/-- Signed coefficients can cancel the purported tropical leading term. -/
theorem signed_cancellation :
    ((Polynomial.X ^ 2 + Polynomial.X ^ 7 : Polynomial ℤ) -
      Polynomial.X ^ 2) = Polynomial.X ^ 7 := by
  ring

/-- A modular pruning claim does not require equality of valuations. -/
theorem modular_prune (term p : ℕ) (h : 2 ^ p ∣ term) :
    term % (2 ^ p) = 0 := Nat.mod_eq_zero_of_dvd h

#print axioms IndependentETH.Tropical.coeff_generating
#print axioms IndependentETH.Tropical.energy_eq_zero_iff
#print axioms IndependentETH.Tropical.count_satisfying
#print axioms IndependentETH.Tropical.monomial_times
#print axioms IndependentETH.Tropical.monomial_plus_equal
#print axioms IndependentETH.Tropical.signed_cancellation
#print axioms IndependentETH.Tropical.modular_prune

end IndependentETH.Tropical
