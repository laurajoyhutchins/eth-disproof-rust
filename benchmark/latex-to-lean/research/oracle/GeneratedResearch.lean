import Mathlib
import ResearchRG01.Article
import ResearchRG03.Article
import ResearchRS02.Article
import ResearchRS03.Article
import ResearchRS04.Article
import ResearchRC01.Article
import ResearchRC02.Article
import ResearchRC03.Article

/- This checks the compiler-generated declarations, not handwritten gold versions.
   Distinguish definitional equivalence of statements from proof of a statement. -/
namespace ResearchGenerated

theorem rg03_exact_statement :
    ResearchRG03.claim0 ↔
      (∀ (a b c d : ℝ), a * c + b * d = b * d + a * c) := by
  rfl

theorem rg03_proof : ResearchRG03.claim0 :=
  rg03_exact_statement.mpr (by
    intro a b c d
    ring)


theorem rs02_reconstruction_first_exact :
    ResearchRS02.claim0 ↔
      (∀ (x y : ℝ), (x + y) / 2 + (x - y) / 2 = x) := by
  rfl

theorem rs02_reconstruction_second_exact :
    ResearchRS02.claim1 ↔
      (∀ (x y : ℝ), (x + y) / 2 - (x - y) / 2 = y) := by
  rfl

theorem rs02_first_proof : ResearchRS02.claim0 :=
  rs02_reconstruction_first_exact.mpr (by
    intro x y
    ring)

theorem rs02_second_proof : ResearchRS02.claim1 :=
  rs02_reconstruction_second_exact.mpr (by
    intro x y
    ring)

#print ResearchRG01.claim0
#print ResearchRG01.claim1
#print ResearchRG03.claim0
#print ResearchRS02.claim0
#print ResearchRS02.claim1
#print ResearchRS03.claim0
#print ResearchRS03.claim1
#print ResearchRS04.claim0
#print ResearchRS04.claim1
#print ResearchRC01.claim0
#print ResearchRC02.claim0
#print ResearchRC03.claim0

#print axioms ResearchGenerated.rg03_exact_statement
#print axioms ResearchGenerated.rg03_proof

#print axioms ResearchGenerated.rs02_reconstruction_first_exact
#print axioms ResearchGenerated.rs02_reconstruction_second_exact
#print axioms ResearchGenerated.rs02_first_proof
#print axioms ResearchGenerated.rs02_second_proof
