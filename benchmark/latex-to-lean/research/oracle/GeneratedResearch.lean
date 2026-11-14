import Mathlib
import ResearchRG03.Article
import ResearchRS02.Article
import ResearchRC02.Article

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

#print ResearchRG03.claim0
#print ResearchRS02.claim0
#print ResearchRS02.claim1
#print ResearchRC02.claim0

#print axioms ResearchGenerated.rg03_exact_statement
#print axioms ResearchGenerated.rg03_proof
