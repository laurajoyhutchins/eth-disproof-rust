import Mathlib
import MutationMRG03.Article
import MutationMRS02.Article
import MutationMRC02.Article

/-! Adversarial source fidelity: false mathematics must remain false.
    Every claim refers to Leanify's source-derived declaration. -/
namespace ResearchMutations

theorem mrg03_exact :
    MutationMRG03.claim0 ↔
      (∀ (a b c d : ℝ), a * c + b * d = b * d - a * c) := by
  rfl

theorem mrg03_refuted : ¬ MutationMRG03.claim0 := by
  intro h
  have hx := (mrg03_exact.mp h) 1 0 1 0
  norm_num at hx

theorem mrs02_preserved_exact :
    MutationMRS02.claim0 ↔
      (∀ (x y : ℝ), (x + y) / 2 + (x - y) / 2 = x) := by
  rfl

theorem mrs02_preserved_true : MutationMRS02.claim0 :=
  mrs02_preserved_exact.mpr (by
    intro x y
    ring)

theorem mrs02_changed_exact :
    MutationMRS02.claim1 ↔
      (∀ (x y : ℝ), (x + y) / 2 - (x - y) / 2 = x) := by
  rfl

theorem mrs02_changed_refuted : ¬ MutationMRS02.claim1 := by
  intro h
  have hx := (mrs02_changed_exact.mp h) 1 0
  norm_num at hx

theorem mrc02_exact :
    MutationMRC02.claim0 ↔
      (((Nat.choose (Nat.floor (4 : ℝ)) (Nat.floor (2 : ℝ)) : ℕ) : ℝ) = 5) := by
  rfl

theorem mrc02_refuted : ¬ MutationMRC02.claim0 := by
  intro h
  have hx := mrc02_exact.mp h
  norm_num at hx

#print axioms ResearchMutations.mrg03_exact
#print axioms ResearchMutations.mrg03_refuted
#print axioms ResearchMutations.mrs02_preserved_exact
#print axioms ResearchMutations.mrs02_preserved_true
#print axioms ResearchMutations.mrs02_changed_exact
#print axioms ResearchMutations.mrs02_changed_refuted
#print axioms ResearchMutations.mrc02_exact
#print axioms ResearchMutations.mrc02_refuted
