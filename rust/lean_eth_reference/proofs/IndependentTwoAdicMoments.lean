import Mathlib

/-!
# Exact finite matching-class and weighted-port moments

This file proves *actual finite sums over independent labels*, not
only a postulated mean-value interface. A matching is represented by
one independent ordered endpoint-label pair per edge. Each shore's
real-port load is represented by one independent symbol per vertex,
weighted by that vertex's degree.

The proofs use no probability measure, floating-point arithmetic,
`sorry` or `admit`. The remaining source-specific bridge must
identify these independent product spaces with restrictions of an
actual bipartite graph's uniformly random vertex labeling and combine
the moments with one exact sequential conditional-expectation score.

These facts do not verify the source's altered Cauchy deformation
away from T=0, two-adic truncation, or recursive counting.
-/

namespace TwoAdicIndependentMoments

open scoped BigOperators

/--
Sum of a multiplicatively separable weight over every independent
vertex/edge-local labeling equals the product of its local sums.
The index can be either source vertices or disjoint matching edges.
-/
theorem independent_label_product_sum
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (weight : V → A → ℚ) :
    (∑ labels ∈ Fintype.piFinset
      (fun _ : V => (Finset.univ : Finset A)),
      ∏ v, weight v (labels v)) =
      ∏ v, ∑ symbol : A, weight v symbol := by
  classical
  rw [Finset.prod_univ_sum]

/--
One symbol is distinguished by a weight `hit`. The other
`card A - 1` choices contribute one. This identity also
holds for a singleton alphabet.
-/
theorem single_symbol_exponential_sum
    {A : Type*} [Fintype A] [DecidableEq A]
    (target : A) (hit : ℚ) :
    (∑ x : A, if x = target then hit else (1 : ℚ)) =
      (Fintype.card A : ℚ) - 1 + hit := by
  classical
  calc
    (∑ x : A, if x = target then hit else (1 : ℚ)) =
      ∑ x : A, ((1 : ℚ) +
        (if x = target then hit - 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = target <;> simp [hx]
    _ = (∑ _x : A, (1 : ℚ)) +
        (∑ x : A, if x = target then hit - 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (Fintype.card A : ℚ) + (hit - 1) := by simp
    _ = (Fintype.card A : ℚ) - 1 + hit := by ring

/--
A matching's ordered-class exponential moment, in exact unnormalized
form. An element of `E` is one edge with its independent pair label;
`A` can be the source ordered-pair alphabet.

When `hit = 2`, the right side is `(D+1)^m`,
where `D=card A` and `m=card E`.
-/
theorem matching_class_exponential_moment
    {E A : Type*} [Fintype E] [DecidableEq E]
    [Fintype A] [DecidableEq A]
    (target : A) (hit : ℚ) :
    (∑ labels ∈ Fintype.piFinset
      (fun _ : E => (Finset.univ : Finset A)),
      ∏ e, (if labels e = target then hit else (1 : ℚ))) =
    ((Fintype.card A : ℚ) - 1 + hit) ^ Fintype.card E := by
  classical
  calc
    _ = ∏ _e : E, (∑ x : A, if x = target then hit else (1 : ℚ)) := by
      exact independent_label_product_sum
        (fun (_e : E) (x : A) => if x = target then hit else 1)
    _ = ∏ _e : E, ((Fintype.card A : ℚ) - 1 + hit) := by
      apply Finset.prod_congr rfl
      intro _ _
      exact single_symbol_exponential_sum target hit
    _ = ((Fintype.card A : ℚ) - 1 + hit) ^ Fintype.card E := by
      simp

/-- Precisely the numerator of the source matching moment. -/
theorem matching_two_exponential_moment
    {E A : Type*} [Fintype E] [DecidableEq E]
    [Fintype A] [DecidableEq A] (target : A) :
    (∑ labels ∈ Fintype.piFinset
      (fun _ : E => (Finset.univ : Finset A)),
      ∏ e, (if labels e = target then (2 : ℚ) else 1)) =
    ((Fintype.card A : ℚ) + 1) ^ Fintype.card E := by
  convert matching_class_exponential_moment target (2 : ℚ) using 1 <;> ring

/--
A symbol-port exponential moment on an actual vertex-degree array.
Each vertex contributes either its entire degree or zero, with one
uniform independent symbol. Unlike an unweighted occupancy model,
high-degree vertices are never split between symbol bins.
-/
theorem degree_weighted_symbol_port_moment
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (degree : V → ℕ) (target : A) (z : ℚ) :
    (∑ labels ∈ Fintype.piFinset
      (fun _ : V => (Finset.univ : Finset A)),
      ∏ v, (if labels v = target then z ^ degree v else (1 : ℚ))) =
    ∏ v, ((Fintype.card A : ℚ) - 1 + z ^ degree v) := by
  classical
  calc
    _ = ∏ v : V, (∑ x : A,
        if x = target then z ^ degree v else (1 : ℚ)) := by
      exact independent_label_product_sum
        (fun v x => if x = target then z ^ degree v else 1)
    _ = ∏ v, ((Fintype.card A : ℚ) - 1 + z ^ degree v) := by
      apply Finset.prod_congr rfl
      intro v _
      exact single_symbol_exponential_sum target (z ^ degree v)

/--
Specialization to two independent endpoint labels on every matching
edge, one of the source's `D=b²` ordered classes. This proves the
moment without assuming any probabilistic estimate.
-/
theorem matching_ordered_pair_moment
    {E : Type*} [Fintype E] [DecidableEq E]
    (b : ℕ) (target : Fin b × Fin b) :
    (∑ labels ∈ Fintype.piFinset
      (fun _ : E => (Finset.univ : Finset (Fin b × Fin b))),
      ∏ e, (if labels e = target then (2 : ℚ) else 1)) =
    (((b * b : ℕ) : ℚ) + 1) ^ Fintype.card E := by
  rw [matching_two_exponential_moment]
  simp [Fintype.card_prod]

#print axioms TwoAdicIndependentMoments.independent_label_product_sum
#print axioms TwoAdicIndependentMoments.single_symbol_exponential_sum
#print axioms TwoAdicIndependentMoments.matching_class_exponential_moment
#print axioms TwoAdicIndependentMoments.matching_two_exponential_moment
#print axioms TwoAdicIndependentMoments.degree_weighted_symbol_port_moment
#print axioms TwoAdicIndependentMoments.matching_ordered_pair_moment

end TwoAdicIndependentMoments
