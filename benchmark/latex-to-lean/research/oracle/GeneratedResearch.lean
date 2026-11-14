import Mathlib
import ResearchRG01.Article
import ResearchRG03.Article
import ResearchRS02.Article
import ResearchRS03.Article
import ResearchRS04.Article
import ResearchRC01.Article
import ResearchRC02.Article
import ResearchRC03.Article

/-! Faithfulness tests against original mathematical expressions, NOT mere
    provability of a true proposition. Every theorem is checked by the Lean kernel.
    The RC01 formula is interpreted over the integers embedded in the reals, as
    specified by Leanify's source-language arithmetic semantics. -/
namespace ResearchGenerated

-- Verify the two user-defined coordinate operations, not just their theorems.
theorem rg01_u_denotation (x y : ℝ) : ResearchRG01.u x y = y := by rfl
theorem rg01_v_denotation (x y : ℝ) : ResearchRG01.v x y = x := by rfl

theorem rg01_claim0_exact :
    ResearchRG01.claim0 ↔
    (∀ (x y : ℝ), (fun (_a b : ℝ) => b)
        ((fun (_a b : ℝ) => b) x y)
        ((fun (a _b : ℝ) => a) x y) = x) := by
  rfl

theorem rg01_claim1_exact :
    ResearchRG01.claim1 ↔
    (∀ (x y : ℝ), (fun (a _b : ℝ) => a)
        ((fun (_a b : ℝ) => b) x y)
        ((fun (a _b : ℝ) => a) x y) = y) := by
  rfl

theorem rg03_exact_statement :
    ResearchRG03.claim0 ↔
      (∀ (a b c d : ℝ), a * c + b * d = b * d + a * c) := by
  rfl

theorem rs02_reconstruction_first_exact :
    ResearchRS02.claim0 ↔
      (∀ (x y : ℝ), (x + y) / 2 + (x - y) / 2 = x) := by
  rfl

theorem rs02_reconstruction_second_exact :
    ResearchRS02.claim1 ↔
      (∀ (x y : ℝ), (x + y) / 2 - (x - y) / 2 = y) := by
  rfl

theorem rs03_even_denotation (x y : ℝ) :
    ResearchRS03.e x y = (x + y) / 2 := by rfl
theorem rs03_odd_denotation (x y : ℝ) :
    ResearchRS03.o x y = (x - y) / 2 := by rfl

theorem rs03_claim0_exact :
    ResearchRS03.claim0 ↔
    (∀ (x y : ℝ), (y + x) / 2 = (x + y) / 2) := by
  rfl

theorem rs03_claim1_exact :
    ResearchRS03.claim1 ↔
    (∀ (x y : ℝ), (y - x) / 2 = -((x - y) / 2)) := by
  rfl

theorem rs04_even_denotation (x y : ℝ) :
    ResearchRS04.e x y = (x + y) / 2 := by rfl
theorem rs04_odd_denotation (x y : ℝ) :
    ResearchRS04.o x y = (x - y) / 2 := by rfl

theorem rs04_claim0_exact :
    ResearchRS04.claim0 ↔
    (∀ (x y : ℝ),
      (((x + y) / 2 + (x + y) / 2) / 2) = (x + y) / 2) := by
  rfl

theorem rs04_claim1_exact :
    ResearchRS04.claim1 ↔
    (∀ (x y : ℝ),
      (((x - y) / 2 - (-((x - y) / 2))) / 2) = (x - y) / 2) := by
  rfl

-- Explicit mathematical interpretation of the nonnegative-integer binomial
-- assertion. The bounded sum is over integers, with real-valued summands;
-- the bound variable in the original paper is a natural number embedded in ℝ.
theorem rc01_exact_statement :
    ResearchRC01.claim0 ↔
    (∀ (x : ℝ), (∃ n : ℕ, (n : ℝ) = x) →
      (Finset.Icc (Int.ceil (0 : ℝ)) (Int.floor x)).sum
        (fun k : ℤ => ((Nat.choose (Nat.floor x) (Nat.floor (k : ℝ)) : ℕ) : ℝ))
        = (2 : ℝ) ^ (Int.floor x)) := by
  rfl

theorem rc02_exact_statement :
    ResearchRC02.claim0 ↔
      (((Nat.choose (Nat.floor (4 : ℝ)) (Nat.floor (2 : ℝ)) : ℕ) : ℝ) = 6) := by
  rfl

theorem rc03_exact_statement :
    ResearchRC03.claim0 ↔
     (((Nat.choose (Nat.floor (3 : ℝ)) (Nat.floor (0 : ℝ)) : ℕ) : ℝ) +
      ((Nat.choose (Nat.floor (3 : ℝ)) (Nat.floor (1 : ℝ)) : ℕ) : ℝ) +
      ((Nat.choose (Nat.floor (3 : ℝ)) (Nat.floor (2 : ℝ)) : ℕ) : ℝ) +
      ((Nat.choose (Nat.floor (3 : ℝ)) (Nat.floor (3 : ℝ)) : ℕ) : ℝ) = 8) := by
  rfl

-- Mathematical proofs are separately tracked from the source-equivalence gate.
theorem rg03_proof : ResearchRG03.claim0 :=
  rg03_exact_statement.mpr (by intro a b c d; ring)
theorem rs02_first_proof : ResearchRS02.claim0 :=
  rs02_reconstruction_first_exact.mpr (by intro x y; ring)
theorem rs02_second_proof : ResearchRS02.claim1 :=
  rs02_reconstruction_second_exact.mpr (by intro x y; ring)

-- Thirteen claim equivalences, plus denotation checks for declared symbols.
#print axioms ResearchGenerated.rg01_claim0_exact
#print axioms ResearchGenerated.rg01_claim1_exact
#print axioms ResearchGenerated.rg03_exact_statement
#print axioms ResearchGenerated.rs02_reconstruction_first_exact
#print axioms ResearchGenerated.rs02_reconstruction_second_exact
#print axioms ResearchGenerated.rs03_claim0_exact
#print axioms ResearchGenerated.rs03_claim1_exact
#print axioms ResearchGenerated.rs04_claim0_exact
#print axioms ResearchGenerated.rs04_claim1_exact
#print axioms ResearchGenerated.rc01_exact_statement
#print axioms ResearchGenerated.rc02_exact_statement
#print axioms ResearchGenerated.rc03_exact_statement

#print axioms ResearchGenerated.rg01_u_denotation
#print axioms ResearchGenerated.rg01_v_denotation
#print axioms ResearchGenerated.rs03_even_denotation
#print axioms ResearchGenerated.rs03_odd_denotation
#print axioms ResearchGenerated.rs04_even_denotation
#print axioms ResearchGenerated.rs04_odd_denotation
#print axioms ResearchGenerated.rg03_proof
#print axioms ResearchGenerated.rs02_first_proof
#print axioms ResearchGenerated.rs02_second_proof
