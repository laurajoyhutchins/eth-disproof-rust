import Mathlib

/-!
# Exact finite matching-class and weighted-port moments

This file proves *actual finite sums over independent labels*, not
only a postulated mean-value interface. A matching is represented by
one independent ordered endpoint-label pair per edge. Each shore's
real-port load is represented by one independent symbol per vertex,
weighted by that vertex's degree.

The proofs use no probability measure, floating-point arithmetic,
unproved placeholders. The remaining source-specific bridge must
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
A finite product of integer powers is the power of their exponent sum.
This bridges the local product moments to the exact exponential load
counts used by the source probability argument.
-/
theorem product_of_powers_is_power_of_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (z : ℚ) (exponent : V → ℕ) :
    (∏ v : V, z ^ exponent v) =
      z ^ (∑ v : V, exponent v) := by
  classical
  have h (s : Finset V) :
      (∏ v ∈ s, z ^ exponent v) =
        z ^ (∑ v ∈ s, exponent v) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert v s hv ih =>
        simp [hv, ih, pow_add]
  exact h Finset.univ

/--
The exact real-port exponential is a product of independent local
degree factors. A vertex's degree is counted whole, never split.
-/
theorem port_power_equals_local_product
    {V A : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq A] (labels : V → A)
    (target : A) (degree : V → ℕ) (z : ℚ) :
    z ^ (∑ v : V,
      if labels v = target then degree v else 0) =
      ∏ v, (if labels v = target then z ^ degree v else (1 : ℚ)) := by
  classical
  calc
    _ = ∏ v : V,
        z ^ (if labels v = target then degree v else 0) := by
      symm
      exact product_of_powers_is_power_of_sum z
        (fun v => if labels v = target then degree v else 0)
    _ = ∏ v : V,
        (if labels v = target then z ^ degree v else (1 : ℚ)) := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : labels v = target <;> simp [hv]

/--
Exact matching-class exponential moment in its `2^X` form,
where `X` is the actual number of edge-local ordered classes
equal to the chosen target.
-/
theorem matching_count_power_moment
    {E A : Type*} [Fintype E] [DecidableEq E]
    [Fintype A] [DecidableEq A] (target : A) :
    (∑ labels ∈ Fintype.piFinset
      (fun _ : E => (Finset.univ : Finset A)),
      (2 : ℚ) ^ (∑ e : E,
        if labels e = target then 1 else 0)) =
    ((Fintype.card A : ℚ) + 1) ^ Fintype.card E := by
  classical
  calc
    _ = (∑ labels ∈ Fintype.piFinset
        (fun _ : E => (Finset.univ : Finset A)),
        ∏ e, (if labels e = target then (2 : ℚ) else 1)) := by
      apply Finset.sum_congr rfl
      intro labels _
      exact port_power_equals_local_product
        labels target (fun _ => 1) (2 : ℚ)
    _ = ((Fintype.card A : ℚ) + 1) ^ Fintype.card E :=
      matching_two_exponential_moment target

/--
Exact degree-weighted real-port exponential moment in `z^C` form,
where C is the total real edge incidence load of one symbol.
-/
theorem degree_weighted_port_power_moment
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (degree : V → ℕ) (target : A) (z : ℚ) :
    (∑ labels ∈ Fintype.piFinset
      (fun _ : V => (Finset.univ : Finset A)),
      z ^ (∑ v : V,
        if labels v = target then degree v else 0)) =
    ∏ v, ((Fintype.card A : ℚ) - 1 + z ^ degree v) := by
  classical
  calc
    _ = (∑ labels ∈ Fintype.piFinset
        (fun _ : V => (Finset.univ : Finset A)),
        ∏ v, (if labels v = target then z ^ degree v else (1 : ℚ))) := by
      apply Finset.sum_congr rfl
      intro labels _
      exact port_power_equals_local_product labels target degree z
    _ = ∏ v, ((Fintype.card A : ℚ) - 1 + z ^ degree v) :=
      degree_weighted_symbol_port_moment degree target z

/--
Divide the matching moment by the exact number D^m of equally
weighted labelings. This is the rational mean
`((D+1)/D)^m`, not a floating-point approximation.
-/
theorem normalized_matching_count_moment
    {E A : Type*} [Fintype E] [DecidableEq E]
    [Fintype A] [DecidableEq A] (target : A) :
    (∑ labels ∈ Fintype.piFinset
      (fun _ : E => (Finset.univ : Finset A)),
      (2 : ℚ) ^ (∑ e : E,
        if labels e = target then 1 else 0)) /
      (Fintype.card A : ℚ) ^ Fintype.card E =
    (((Fintype.card A : ℚ) + 1) /
      (Fintype.card A : ℚ)) ^ Fintype.card E := by
  rw [matching_count_power_moment]
  rw [div_pow]

/--
Normalize the exact port moment by the number `r^|V|` of
equally likely vertex-symbol labelings. The result is an exact
product of the source's per-vertex rational port factors.
-/
theorem normalized_degree_weighted_port_moment
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (degree : V → ℕ) (target : A) (z : ℚ) :
    (∑ labels ∈ Fintype.piFinset
      (fun _ : V => (Finset.univ : Finset A)),
      z ^ (∑ v : V,
        if labels v = target then degree v else 0)) /
      (Fintype.card A : ℚ) ^ Fintype.card V =
    ∏ v, (((Fintype.card A : ℚ) - 1 + z ^ degree v) /
      (Fintype.card A : ℚ)) := by
  classical
  calc
    _ = (∏ v : V, ((Fintype.card A : ℚ) - 1 + z ^ degree v)) /
        (∏ _v : V, (Fintype.card A : ℚ)) := by
      rw [degree_weighted_port_power_moment]
      simp
    _ = ∏ v : V, (((Fintype.card A : ℚ) - 1 + z ^ degree v) /
        (Fintype.card A : ℚ)) := by
      rw [Finset.prod_div_distrib]

/--
The same normalized port moment in the source's factor form
`product_v (1 + (z^degree_v - 1)/r)`, with no real
approximations or independent stochastic assumptions.
-/
theorem normalized_degree_weighted_port_source_factor
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (degree : V → ℕ) (target : A) (z : ℚ) :
    (∑ labels ∈ Fintype.piFinset
      (fun _ : V => (Finset.univ : Finset A)),
      z ^ (∑ v : V,
        if labels v = target then degree v else 0)) /
      (Fintype.card A : ℚ) ^ Fintype.card V =
    ∏ v, (1 + (z ^ degree v - 1) /
      (Fintype.card A : ℚ)) := by
  rw [normalized_degree_weighted_port_moment]
  have hr : (Fintype.card A : ℚ) ≠ 0 := by
    have hc : 0 < Fintype.card A :=
      Fintype.card_pos_iff.mpr ⟨target⟩
    exact_mod_cast (Nat.ne_of_gt hc)
  apply Finset.prod_congr rfl
  intro v _
  field_simp
  ring

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
#print axioms TwoAdicIndependentMoments.product_of_powers_is_power_of_sum
#print axioms TwoAdicIndependentMoments.port_power_equals_local_product
#print axioms TwoAdicIndependentMoments.matching_count_power_moment
#print axioms TwoAdicIndependentMoments.degree_weighted_port_power_moment
#print axioms TwoAdicIndependentMoments.normalized_matching_count_moment
#print axioms TwoAdicIndependentMoments.normalized_degree_weighted_port_moment
#print axioms TwoAdicIndependentMoments.normalized_degree_weighted_port_source_factor
#print axioms TwoAdicIndependentMoments.matching_ordered_pair_moment

end TwoAdicIndependentMoments
