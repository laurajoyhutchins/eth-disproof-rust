import Mathlib
import ACC.FactoredOperator

/-!
# OpenAI's displayed zero-deformation port glue: a conditional adapter

The exact October 25, 2026 quantitative-contraction appendix defines
  F(T) = ∑ X,Y, A(Y) B(X) ∏_i ℓ_(Y_i)((W(T) X)_i)
where ℓ_false(z)=1-z, ℓ_true(z)=z, and states W(0)=I.

This file independently proves the finite algebraic consequence of that
SPECIFIED FORMULA given the explicit hypothesis W0 = identity.

It does NOT import or compile the original Lean packet constructor, prove
its W(0)=I lemma, or establish its deformed/two-adic algorithm. Keeping the
hypothesis visible is an important source-faithfulness boundary.
-/

namespace ACC.OpenAIZeroGlue

open scoped BigOperators

def bitValue (x : Bool) : ℤ := if x then 1 else 0

def selectBit (y : Bool) (z : ℤ) : ℤ :=
  if y then z else 1 - z

theorem selector_on_bit (y x : Bool) :
    selectBit y (bitValue x) =
      if y = x then (1 : ℤ) else 0 := by
  cases y <;> cases x <;> norm_num [selectBit, bitValue]

/-- The original paper's zero-deformation selector product, with the
    explicit value of W(0) passed as an argument. -/
def zeroGlue {n : ℕ}
    (W0 : (Fin n → Bool) → Fin n → ℤ)
    (out input : Fin n → Bool) : ℤ :=
  ∏ i : Fin n, selectBit (out i) (W0 input i)

/-- The stated condition W(0)=I is precisely the hypothesis needed to
    identify the source's selector product with our factored identity.
    No source theorem is silently assumed. -/
theorem zeroGlue_eq_identity {n : ℕ}
    (W0 : (Fin n → Bool) → Fin n → ℤ)
    (hW0 : ∀ input i, W0 input i = bitValue (input i))
    (out input : Fin n → Bool) :
    zeroGlue W0 out input =
      (ACC.FactoredOperator.TensorKernel.identity n).eval out input := by
  classical
  change
    (∏ i : Fin n, selectBit (out i) (W0 input i)) =
      ∏ i : Fin n,
        ACC.FactoredOperator.WireMatrix.identity.lookup (out i) (input i)
  apply Finset.prod_congr rfl
  intro i hi
  rw [hW0 input i, selector_on_bit,
    ACC.FactoredOperator.WireMatrix.identity_lookup]

/-- At zero deformation, the paper's double sum reduces exactly
    to the ordinary diagonal contraction, for arbitrary integer-valued
    lifted tensor products A and B. -/
theorem zero_contraction_is_diagonal {n : ℕ}
    (W0 : (Fin n → Bool) → Fin n → ℤ)
    (hW0 : ∀ input i, W0 input i = bitValue (input i))
    (A B : (Fin n → Bool) → ℤ) :
    (∑ input ∈ Fintype.piFinset
       (fun _ : Fin n => (Finset.univ : Finset Bool)),
      ∑ out ∈ Fintype.piFinset
        (fun _ : Fin n => (Finset.univ : Finset Bool)),
        A out * B input * zeroGlue W0 out input) =
    ∑ input ∈ Fintype.piFinset
      (fun _ : Fin n => (Finset.univ : Finset Bool)),
      A input * B input := by
  classical
  apply Finset.sum_congr rfl
  intro input hinput
  calc
    (∑ out ∈ Fintype.piFinset
        (fun _ : Fin n => (Finset.univ : Finset Bool)),
        A out * B input * zeroGlue W0 out input) =
      ∑ out ∈ Fintype.piFinset
        (fun _ : Fin n => (Finset.univ : Finset Bool)),
        if out = input then A out * B input else 0 := by
      apply Finset.sum_congr rfl
      intro out hout
      rw [zeroGlue_eq_identity W0 hW0 out input,
        ACC.FactoredOperator.TensorKernel.identity_eval]
      split_ifs <;> ring
    _ = A input * B input := by
      simp [hinput]

#print axioms ACC.OpenAIZeroGlue.selector_on_bit
#print axioms ACC.OpenAIZeroGlue.zeroGlue_eq_identity
#print axioms ACC.OpenAIZeroGlue.zero_contraction_is_diagonal

end ACC.OpenAIZeroGlue
