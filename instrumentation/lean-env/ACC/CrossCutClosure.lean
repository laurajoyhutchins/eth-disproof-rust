import Mathlib
import ACC.FactoredOperator

/-!
# Exact separated boundary contractions

A sum of chi products of left/right operators applied to a sum of d
separated left/right states has an *explicit* chi*d-term representation.

The theorem is an exact equality over the integers. It does not assert
that chi*d terms are minimal, nor charge bit costs or find a good cut.

The matching-equality family then witnesses why the chosen cut matters:
it is a product of m two-wire factors but has rank 2^m across the
grouped a|b cut. A factorization through d separated terms must have
d >= 2^m, via the pinned Mathlib matrix-rank bounds.
-/

namespace ACC.CrossCutClosure

open scoped BigOperators
open ACC.FactoredOperator

/-- Exchange two nested groups of independent finite sums. -/
private theorem exchange_four
    {S T U V : Type*}
    [Fintype S] [Fintype T] [Fintype U] [Fintype V]
    (f : S → T → U → V → ℤ) :
    (∑ s : S, ∑ t : T, ∑ u : U, ∑ v : V, f s t u v) =
    ∑ u : U, ∑ v : V, ∑ s : S, ∑ t : T, f s t u v := by
  classical
  calc
    _ = ∑ s : S, ∑ u : U, ∑ t : T, ∑ v : V, f s t u v := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = ∑ u : U, ∑ s : S, ∑ t : T, ∑ v : V, f s t u v :=
      Finset.sum_comm
    _ = ∑ u : U, ∑ s : S, ∑ v : V, ∑ t : T, f s t u v := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = ∑ u : U, ∑ v : V, ∑ s : S, ∑ t : T, f s t u v := by
      apply Finset.sum_congr rfl
      intro u _
      exact Finset.sum_comm

/-- The denotation of a chi-term cross-cut operator on a d-term input. -/
noncomputable def applyCross
    {L R : Type*} [Fintype L] [Fintype R]
    {chi d : ℕ}
    (A : Fin chi → L → L → ℤ)
    (B : Fin chi → R → R → ℤ)
    (u : Fin d → L → ℤ)
    (v : Fin d → R → ℤ)
    (x : L) (y : R) : ℤ :=
  ∑ a : L, ∑ b : R,
    (∑ alpha : Fin chi, A alpha x a * B alpha y b) *
    (∑ j : Fin d, u j a * v j b)

/-- The output's explicit separated form. Its term indices form
    Fin chi × Fin d, hence there are chi*d (possibly zero) terms. -/
noncomputable def applySeparated
    {L R : Type*} [Fintype L] [Fintype R]
    {chi d : ℕ}
    (A : Fin chi → L → L → ℤ)
    (B : Fin chi → R → R → ℤ)
    (u : Fin d → L → ℤ)
    (v : Fin d → R → ℤ)
    (x : L) (y : R) : ℤ :=
  ∑ alpha : Fin chi, ∑ j : Fin d,
    (∑ a : L, A alpha x a * u j a) *
    (∑ b : R, B alpha y b * v j b)

/-- Exact cross-cut closure. The output description is not obtained
    by enumerating all (x,y), although the denotational sums here are
    not a certified executable implementation. -/
theorem applyCross_eq_separated
    {L R : Type*} [Fintype L] [Fintype R]
    {chi d : ℕ}
    (A : Fin chi → L → L → ℤ)
    (B : Fin chi → R → R → ℤ)
    (u : Fin d → L → ℤ)
    (v : Fin d → R → ℤ)
    (x : L) (y : R) :
    applyCross A B u v x y = applySeparated A B u v x y := by
  classical
  unfold applyCross applySeparated
  calc
    (∑ a : L, ∑ b : R,
      (∑ alpha : Fin chi, A alpha x a * B alpha y b) *
      (∑ j : Fin d, u j a * v j b)) =
      ∑ a : L, ∑ b : R, ∑ alpha : Fin chi, ∑ j : Fin d,
        (A alpha x a * B alpha y b) * (u j a * v j b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro alpha _
      rw [Finset.mul_sum]
    _ = ∑ alpha : Fin chi, ∑ j : Fin d, ∑ a : L, ∑ b : R,
          (A alpha x a * B alpha y b) * (u j a * v j b) :=
      exchange_four _
    _ = ∑ alpha : Fin chi, ∑ j : Fin d,
          (∑ a : L, A alpha x a * u j a) *
          (∑ b : R, B alpha y b * v j b) := by
      apply Finset.sum_congr rfl
      intro alpha _
      apply Finset.sum_congr rfl
      intro j _
      calc
        (∑ a : L, ∑ b : R,
          (A alpha x a * B alpha y b) * (u j a * v j b)) =
          ∑ a : L, ∑ b : R,
            (A alpha x a * u j a) * (B alpha y b * v j b) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring
        _ = (∑ a : L, A alpha x a * u j a) *
            (∑ b : R, B alpha y b * v j b) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]

theorem separated_term_count (chi d : ℕ) :
    Fintype.card (Fin chi × Fin d) = chi * d := by
  simp

/-- The source identity interaction is the grouped-cut matching matrix. -/
theorem matching_rank (m : ℕ) :
    Matrix.rank
      (fun a b : Fin m → Bool =>
        ((TensorKernel.identity m).eval a b : ℚ)) = 2 ^ m :=
  TensorKernel.identity_rank m

/-- An arbitrary decomposition of the m-pair equality matching into
    d separated terms forces d >= 2^m (over the rational field).
    This does not rule out a small *locally paired* factorization. -/
theorem matching_separated_lower_bound
    (m d : ℕ)
    (u v : Fin d → (Fin m → Bool) → ℚ)
    (h : ∀ a b : Fin m → Bool,
      ((TensorKernel.identity m).eval a b : ℚ) =
        ∑ j : Fin d, u j a * v j b) :
    2 ^ m ≤ d := by
  classical
  let U : Matrix (Fin m → Bool) (Fin d) ℚ := fun a j => u j a
  let V : Matrix (Fin d) (Fin m → Bool) ℚ := fun j b => v j b
  have hUV :
      U * V =
        (fun a b : Fin m → Bool =>
          ((TensorKernel.identity m).eval a b : ℚ)) := by
    ext a b
    simp only [Matrix.mul_apply, U, V]
    exact (h a b).symm
  calc
    2 ^ m =
        Matrix.rank
          (fun a b : Fin m → Bool =>
            ((TensorKernel.identity m).eval a b : ℚ)) :=
      (matching_rank m).symm
    _ = (U * V).rank := by rw [hUV]
    _ ≤ U.rank := Matrix.rank_mul_le_left U V
    _ ≤ d := by simpa using Matrix.rank_le_card_width U

/-- A disjoint-pair matching contracts against unary input factors
    with one two-term sum per pair. No global 2^(2m) table is needed. -/
theorem matching_contract
    (m : ℕ)
    (u v : Fin m → Bool → ℤ) :
    (∑ a ∈ Fintype.piFinset
      (fun _ : Fin m => (Finset.univ : Finset Bool)),
      productInput u a *
        (TensorKernel.identity m).applyProduct v a) =
    ∏ i : Fin m, ∑ bit : Bool, u i bit * v i bit := by
  classical
  simp only [TensorKernel.identity_applyProduct, productInput]
  calc
    (∑ a ∈ Fintype.piFinset
      (fun _ : Fin m => (Finset.univ : Finset Bool)),
      (∏ i : Fin m, u i (a i)) *
        (∏ i : Fin m, v i (a i))) =
      ∑ a ∈ Fintype.piFinset
        (fun _ : Fin m => (Finset.univ : Finset Bool)),
        ∏ i : Fin m, u i (a i) * v i (a i) := by
      apply Finset.sum_congr rfl
      intro a _
      exact (Finset.prod_mul_distrib).symm
    _ = ∏ i : Fin m, ∑ bit : Bool, u i bit * v i bit := by
      exact Finset.sum_prod_piFinset
        (Finset.univ : Finset Bool)
        (fun i bit => u i bit * v i bit)

#print axioms ACC.CrossCutClosure.applyCross_eq_separated
#print axioms ACC.CrossCutClosure.matching_separated_lower_bound
#print axioms ACC.CrossCutClosure.matching_contract

end ACC.CrossCutClosure
