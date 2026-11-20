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
    simp only [if_pos h, if_pos hs]
  · have hs : ¬ (∀ clause ∈ φ, clauseTrue a clause = true) := by
      intro hc
      exact h ((energy_eq_zero_iff φ a).mpr hc)
    simp only [if_neg h, if_neg hs]

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

/-- Equality of leading terms is determined by the two data fields;
    positivity evidence is propositionally irrelevant. -/
private theorem term_ext {a b : Term}
    (hd : a.degree = b.degree) (hc : a.count = b.count) : a = b := by
  cases a with
  | mk da ca ha =>
    cases b with
    | mk db cb hb =>
      dsimp at hd hc
      subst db
      subst cb
      rfl

theorem times_comm (a b : Leading) : times a b = times b a := by
  cases a with
  | none => cases b <;> rfl
  | some a =>
      cases b with
      | none => rfl
      | some b =>
          simp only [times]
          apply congrArg Option.some
          apply term_ext
          · exact Nat.add_comm _ _
          · exact Nat.mul_comm _ _

theorem times_assoc (a b c : Leading) :
    times (times a b) c = times a (times b c) := by
  cases a with
  | none => rfl
  | some a =>
      cases b with
      | none => rfl
      | some b =>
          cases c with
          | none => rfl
          | some c =>
              simp only [times]
              apply congrArg Option.some
              apply term_ext
              · exact Nat.add_assoc _ _ _
              · exact Nat.mul_assoc _ _ _

theorem plus_comm (a b : Leading) : plus a b = plus b a := by
  cases a with
  | none => cases b <;> rfl
  | some a =>
      cases b with
      | none => rfl
      | some b =>
          by_cases hab : a.degree < b.degree
          · have hba : ¬ b.degree < a.degree := by omega
            simp [plus, hab, hba]
          · by_cases hba : b.degree < a.degree
            · simp [plus, hab, hba]
            · have heq : a.degree = b.degree := by omega
              simp only [plus, if_neg hab, if_neg hba]
              apply congrArg Option.some
              apply term_ext
              · exact heq
              · exact Nat.add_comm _ _

theorem plus_zero (x : Leading) : plus x none = x := by
  cases x <;> rfl

theorem zero_plus (x : Leading) : plus none x = x := rfl

/-- Addition combines the minimum degree and sums equal-degree multiplicities. -/
theorem plus_assoc (a b c : Leading) :
    plus (plus a b) c = plus a (plus b c) := by
  cases a with
  | none => rfl
  | some a =>
      cases b with
      | none => rfl
      | some b =>
          cases c with
          | none => simp only [plus_zero]
          | some c =>
              by_cases hab : a.degree < b.degree
              all_goals by_cases hba : b.degree < a.degree
              all_goals by_cases hac : a.degree < c.degree
              all_goals by_cases hca : c.degree < a.degree
              all_goals by_cases hbc : b.degree < c.degree
              all_goals by_cases hcb : c.degree < b.degree
              all_goals
                simp [plus, hab, hba, hac, hca, hbc, hcb,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;>
                  first
                  | rfl
                  | omega
                  | (apply congrArg Option.some
                     apply term_ext <;> omega)

theorem times_zero (x : Leading) : times x none = none := by
  cases x <;> rfl

theorem zero_times (x : Leading) : times none x = none := rfl

/-- Distributivity, including equal minimum degrees and multiplicity ties. -/
theorem times_plus (a b c : Leading) :
    times (plus a b) c = plus (times a c) (times b c) := by
  cases a with
  | none =>
      cases b <;> cases c <;> rfl
  | some a =>
      cases b with
      | none => cases c <;> rfl
      | some b =>
          cases c with
          | none => simp only [times_zero, plus]
          | some c =>
              by_cases hab : a.degree < b.degree
              · have hba : ¬ b.degree < a.degree := by omega
                have hab' : a.degree + c.degree < b.degree + c.degree := by omega
                have hba' : ¬ b.degree + c.degree < a.degree + c.degree := by omega
                simp [plus, times, hab, hba, hab', hba']
              · by_cases hba : b.degree < a.degree
                · have hab' : ¬ a.degree + c.degree < b.degree + c.degree := by omega
                  have hba' : b.degree + c.degree < a.degree + c.degree := by omega
                  simp [plus, times, hab, hba, hab', hba']
                · have heq : a.degree = b.degree := by omega
                  simp [plus, times, heq, Nat.add_mul]

theorem plus_times (a b c : Leading) :
    times a (plus b c) = plus (times a b) (times a c) := by
  rw [times_comm a (plus b c), times_plus, times_comm b a, times_comm c a]

/-- The degree-zero unit is multiplicatively neutral. -/
theorem unit_times (x : Leading) :
    times (monomial 0 1 (by omega)) x = x := by
  cases x with
  | none => rfl
  | some x =>
      simp only [times, monomial]
      apply congrArg Option.some
      apply term_ext <;> simp

theorem times_unit (x : Leading) :
    times x (monomial 0 1 (by omega)) = x := by
  rw [times_comm, unit_times]

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
#print axioms IndependentETH.Tropical.plus_comm
#print axioms IndependentETH.Tropical.plus_assoc
#print axioms IndependentETH.Tropical.times_plus
#print axioms IndependentETH.Tropical.plus_times
#print axioms IndependentETH.Tropical.unit_times
#print axioms IndependentETH.Tropical.times_assoc
#print axioms IndependentETH.Tropical.monomial_times
#print axioms IndependentETH.Tropical.monomial_plus_equal
#print axioms IndependentETH.Tropical.signed_cancellation
#print axioms IndependentETH.Tropical.modular_prune

end IndependentETH.Tropical
