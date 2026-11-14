import Mathlib
import BenchE01.Article
import BenchX01.Article
import BenchX02.Article

namespace GeneratedEquivalence
theorem e01_faithful : BenchE01.claim0 ↔ (∀ (a b : ℝ), a + b = b + a) := by rfl
theorem x01_faithful : BenchX01.claim0 ↔ (∀ x : ℝ, 0 < x ^ 2) := by rfl
theorem x02_faithful : BenchX02.claim0 ↔ (∀ x : ℝ, (1 / x) * x = 1) := by rfl
theorem x02_definedness_faithful : BenchX02.meaningful0 ↔ (∀ x : ℝ, x ≠ 0) := by rfl
theorem e01_generated_provable : BenchE01.claim0 :=
  e01_faithful.mpr (fun a b => add_comm a b)
theorem x01_generated_refutable : ¬ BenchX01.claim0 := by
  intro h
  have hz := (x01_faithful.mp h) 0
  norm_num at hz
theorem x02_definedness_impossible : ¬ BenchX02.meaningful0 := by
  intro h
  exact (x02_definedness_faithful.mp h) 0 rfl
#print axioms GeneratedEquivalence.e01_faithful
#print axioms GeneratedEquivalence.x01_faithful
#print axioms GeneratedEquivalence.x02_faithful
#print axioms GeneratedEquivalence.x02_definedness_faithful
#print axioms GeneratedEquivalence.e01_generated_provable
#print axioms GeneratedEquivalence.x01_generated_refutable
#print axioms GeneratedEquivalence.x02_definedness_impossible
