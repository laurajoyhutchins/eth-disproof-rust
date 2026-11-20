import Mathlib

/-!
# Unit-resolution implication and two-way source refutation

These elementary lemmas justify a checked certificate boundary for
source-derived early pruning of the FINAL #SAT objective. They do not
identify the actual Rust trace checker with Lean, nor do they permit
replacing an intermediate processed-prefix count with a pruned count
when that prefix is observed independently.
-/

namespace IndependentETH.UnitRefutation

abbrev Literal := String × Bool
abbrev Clause := List Literal
abbrev CNF := List Clause
abbrev Partial := String → Option Bool

def extendsPartial (a : String → Bool) (p : Partial) : Prop :=
  ∀ v value, p v = some value → a v = value

def clauseTrue (a : String → Bool) (clause : Clause) : Prop :=
  ∃ lit ∈ clause, a lit.1 = lit.2

def cnfTrue (a : String → Bool) (cnf : CNF) : Prop :=
  ∀ clause ∈ cnf, clauseTrue a clause

def allFalse (p : Partial) (clause : Clause) : Prop :=
  ∀ lit ∈ clause, p lit.1 = some (!lit.2)

/-- An exact clause-only contradiction under a fixed boundary partial
assignment cannot be satisfied by any total completion. -/
theorem empty_reason_sound
    (a : String → Bool) (p : Partial) (clause : Clause)
    (hext : extendsPartial a p) (hfalse : allFalse p clause) :
    ¬ clauseTrue a clause := by
  rintro ⟨lit, hmem, htrue⟩
  have hf := hext lit.1 (!lit.2) (hfalse lit hmem)
  cases lit.2 <;> simp_all

def unitReason (p : Partial) (clause : Clause)
    (v : String) (sign : Bool) : Prop :=
  (v, sign) ∈ clause ∧ p v = none ∧
    ∀ lit ∈ clause, lit ≠ (v, sign) →
      p lit.1 = some (!lit.2)

/-- If a source clause is unit under a partial assignment, every
satisfying extension must have the forced value. This is the sound
primitive used in independently replaying a sequence of reasons. -/
theorem unit_reason_forces
    (a : String → Bool) (p : Partial) (clause : Clause)
    (v : String) (sign : Bool)
    (hext : extendsPartial a p)
    (hsat : clauseTrue a clause)
    (hunit : unitReason p clause v sign) :
    a v = sign := by
  rcases hsat with ⟨lit, hmem, htrue⟩
  rcases hunit with ⟨_, _, hothers⟩
  by_cases h : lit = (v, sign)
  · simpa [h] using htrue
  · have hf := hext lit.1 (!lit.2) (hothers lit hmem h)
    cases lit.2 <;> simp_all

/-- An exhaustive one-v split is a valid refutation when both
branches are incompatible with the source CNF and the same boundary
assumptions. The Rust checker additionally checks each branch's
source-indexed unit trace; that implementation refinement remains open. -/
theorem two_branches_refute
    (cnf : CNF) (p : Partial) (v : String)
    (hfalse : ∀ a, extendsPartial a p →
      a v = false → ¬ cnfTrue a cnf)
    (htrue : ∀ a, extendsPartial a p →
      a v = true → ¬ cnfTrue a cnf) :
    ∀ a, extendsPartial a p → ¬ cnfTrue a cnf := by
  intro a hext
  cases hv : a v with
  | false => exact hfalse a hext hv
  | true => exact htrue a hext hv

/-- The final-count pruning criterion: once the future source CNF is
refuted for a retained boundary assignment, no satisfying total
assignment extending that boundary can contribute to #SAT. -/
theorem future_refutation_eliminates
    (future : CNF) (p : Partial)
    (hrefute : ∀ a, extendsPartial a p → ¬ cnfTrue a future) :
    ¬ ∃ a, extendsPartial a p ∧ cnfTrue a future := by
  rintro ⟨a, ha, hs⟩
  exact hrefute a ha hs

/-- Reusable nogoods are monotone under *extension* of the assumptions
used for a checked contradiction. A cached proof may have been replayed
under fewer assumptions than the original source boundary assignment.
It remains valid under every assignment extending those assumptions. -/
theorem cached_refutation_monotone
    (future : CNF) (weak strong : Partial)
    (hsub : ∀ name value, weak name = some value →
      strong name = some value)
    (hrefute : ∀ a, extendsPartial a weak → ¬ cnfTrue a future) :
    ∀ a, extendsPartial a strong → ¬ cnfTrue a future := by
  intro a hext
  apply hrefute a
  intro name value hw
  exact hext name value (hsub name value hw)

/-- The final natural #SAT sum is unchanged by dropping a processed
prefix's boundary contribution only when its *future* count is certified
zero. The pruned prefix alone is NOT generally equal to the original. -/
theorem contextual_zero_count_preserved {α : Type} (s : Finset α)
    (prefixCount future : α → ℕ) (cachedMatch : α → Prop)
    (hsound : ∀ i ∈ s, cachedMatch i → future i = 0) :
    (∑ i ∈ s, prefixCount i * future i) =
      ∑ i ∈ s, if cachedMatch i then 0 else prefixCount i * future i := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : cachedMatch i
  · simp [hc, hsound i hi hc]
  · simp [hc]

#print axioms empty_reason_sound
#print axioms unit_reason_forces
#print axioms two_branches_refute
#print axioms future_refutation_eliminates
#print axioms cached_refutation_monotone
#print axioms contextual_zero_count_preserved

end IndependentETH.UnitRefutation
