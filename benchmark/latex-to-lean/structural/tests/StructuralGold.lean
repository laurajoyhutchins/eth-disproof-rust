/- These independent oracles are appended after the generated modules.
   No theorem proof is an output of the structural compiler. -/
namespace StructuralAcceptance

theorem rg02_faithful :
    StructuralRG02.claim ↔
    (∀ (x y : ℝ), StructuralRG02.s (StructuralRG02.s ![x,y]) = ![x,y]) := by
  rfl
theorem rg04_faithful :
    StructuralRG04.claim ↔
    (∀ (v : Fin 4 → ℝ),
       StructuralRG04.s (StructuralRG04.t v) =
       StructuralRG04.t (StructuralRG04.s v)) := by
  rfl
theorem rs01_faithful :
    StructuralRS01.claim ↔
      (StructuralRS01.P ^ 2 = (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rfl
theorem rc04_faithful :
    StructuralRC04.claim ↔ (Fintype.card (Fin 2 → Fin 2) = 4) := by
  rfl

theorem rg02_proved : StructuralRG02.claim := by
  intro x y
  ext i
  fin_cases i <;> rfl

theorem rg04_proved : StructuralRG04.claim := by
  intro v
  ext i
  fin_cases i <;> rfl

theorem rs01_proved : StructuralRS01.claim := by
  change StructuralRS01.P ^ 2 = (1 : Matrix (Fin 2) (Fin 2) ℝ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [StructuralRS01.P, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem rc04_proved : StructuralRC04.claim := by
  norm_num [StructuralRC04.claim, Fintype.card_fun]

theorem holdout_reverse_faithful :
    StructuralHVector5.claim ↔
    (∀ (a b c d e : ℝ),
      StructuralHVector5.r (StructuralHVector5.r ![a,b,c,d,e]) = ![a,b,c,d,e]) := by
  rfl
theorem holdout_reverse_proved : StructuralHVector5.claim := by
  intro a b c d e
  ext i
  fin_cases i <;> rfl

theorem holdout_map_proved : StructuralHMap3to2.claim := by
  intro x y z
  rfl
theorem holdout_matrix_proved : StructuralHMatrix3.claim := by
  change StructuralHMatrix3.Q ^ 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [StructuralHMatrix3.Q, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]
theorem holdout_count_proved : StructuralHWords3.claim := by
  norm_num [StructuralHWords3.claim, Fintype.card_fun]

theorem holdout_false_count_refuted : ¬ StructuralHFalseWords3.claim := by
  norm_num [StructuralHFalseWords3.claim, Fintype.card_fun]
theorem holdout_false_swap_refuted : ¬ StructuralHFalseSwap.claim := by
  intro h
  have hx := h 0 1
  have contrad : (0 : ℝ) = 1 := by
    simpa [StructuralHFalseSwap.s] using congrArg (fun v : Fin 2 → ℝ => v 0) hx
  norm_num at contrad

#print axioms StructuralAcceptance.rg02_faithful
#print axioms StructuralAcceptance.rg04_faithful
#print axioms StructuralAcceptance.rs01_faithful
#print axioms StructuralAcceptance.rc04_faithful
#print axioms StructuralAcceptance.rg02_proved
#print axioms StructuralAcceptance.rg04_proved
#print axioms StructuralAcceptance.rs01_proved
#print axioms StructuralAcceptance.rc04_proved
#print axioms StructuralAcceptance.holdout_reverse_faithful
#print axioms StructuralAcceptance.holdout_reverse_proved
#print axioms StructuralAcceptance.holdout_map_proved
#print axioms StructuralAcceptance.holdout_matrix_proved
#print axioms StructuralAcceptance.holdout_count_proved
#print axioms StructuralAcceptance.holdout_false_count_refuted
#print axioms StructuralAcceptance.holdout_false_swap_refuted
