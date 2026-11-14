import Mathlib

open scoped Matrix

/- Independent reference mathematics, NOT candidate compiler output.
   Group actions: coordinate transpositions on products.
   Spectral: eigenvalue ±1 splitting of a pair swap.
   Counting: binomial enumeration and Boolean words. -/
namespace LatexLeanResearchGold

def swap (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1)

theorem swap_involution (p : ℝ × ℝ) : swap (swap p) = p := by
  cases p
  rfl

def swapLeft (p : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) :=
  (swap p.1, p.2)

def swapRight (p : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) :=
  (p.1, swap p.2)

theorem independent_swaps_commute (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    swapLeft (swapRight p) = swapRight (swapLeft p) := by
  rfl

theorem simultaneous_swap_preserves_dot (a b c d : ℝ) :
    a * c + b * d = b * d + a * c := by
  ring

def swapMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem swap_matrix_square : swapMatrix * swapMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

def evenCoord (x y : ℝ) : ℝ := (x + y) / 2
def oddCoord (x y : ℝ) : ℝ := (x - y) / 2

theorem spectral_reconstruction (x y : ℝ) :
    evenCoord x y + oddCoord x y = x ∧
    evenCoord x y - oddCoord x y = y := by
  constructor <;> dsimp [evenCoord, oddCoord] <;> ring

theorem spectral_parity (x y : ℝ) :
    evenCoord y x = evenCoord x y ∧
    oddCoord y x = -oddCoord x y := by
  constructor <;> dsimp [evenCoord, oddCoord] <;> ring

theorem spectral_projectors_idempotent (x y : ℝ) :
    evenCoord (evenCoord x y) (evenCoord x y) = evenCoord x y ∧
    oddCoord (oddCoord x y) (-oddCoord x y) = oddCoord x y := by
  constructor <;> dsimp [evenCoord, oddCoord] <;> ring

theorem choose_four_two : Nat.choose 4 2 = 6 := by decide

theorem choose_three_sum :
    (Finset.range 4).sum (fun k => Nat.choose 3 k) = 8 := by decide

theorem boolean_words_length_two :
    Fintype.card (Bool × Bool) = 4 := by decide

theorem choose_sum (n : ℕ) :
    (Finset.range (n + 1)).sum (fun k => Nat.choose n k) = 2 ^ n := by
  simpa using Nat.sum_range_choose n

#print axioms LatexLeanResearchGold.swap_involution
#print axioms LatexLeanResearchGold.independent_swaps_commute
#print axioms LatexLeanResearchGold.simultaneous_swap_preserves_dot
#print axioms LatexLeanResearchGold.swap_matrix_square
#print axioms LatexLeanResearchGold.spectral_reconstruction
#print axioms LatexLeanResearchGold.spectral_parity
#print axioms LatexLeanResearchGold.spectral_projectors_idempotent
#print axioms LatexLeanResearchGold.choose_four_two
#print axioms LatexLeanResearchGold.choose_three_sum
#print axioms LatexLeanResearchGold.boolean_words_length_two
#print axioms LatexLeanResearchGold.choose_sum
