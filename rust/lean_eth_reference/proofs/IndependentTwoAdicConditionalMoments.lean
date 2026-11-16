import Mathlib

/-!
# Exact conditional moments for partially assigned source vertex labels

A partial assignment is a function `V → Option A`. A committed
vertex ranges over its singleton label; every uncommitted vertex
ranges over the entire finite alphabet. These are actual vertex
assignments, not independently sampled edges.

The finite vertex-port lemma uses the *whole degree* of each
vertex, even in a multigraph. The edge-local matching lemma uses
one pair label for each edge; transporting it to the source's
unrestricted vertex-label space requires a separate verified
endpoint-disjointness argument.

All identities are finite sums in exact rationals. No probabilistic
independence axioms or source algorithm correctness premises appear.
-/

namespace TwoAdicConditionalMoments

open scoped BigOperators

/-- The finite choices available at a vertex after a partial assignment. -/
def admissible {V A : Type*} [DecidableEq A]
    [Fintype A] (fixed : V → Option A) (v : V) : Finset A :=
  match fixed v with
  | some label => {label}
  | none => Finset.univ

/-- A partial vertex assignment fixes exactly the specified vertices. -/
theorem mem_admissible {V A : Type*} [Fintype A] [DecidableEq A]
    (fixed : V → Option A) (v : V) (label : A) :
    label ∈ admissible fixed v ↔
      fixed v = none ∨ fixed v = some label := by
  cases h : fixed v with
  | none => simp [admissible, h]
  | some x => simp [admissible, h, eq_comm]

/-- One symbol port's exact local conditional weight. -/
def localPortMoment {V A : Type*} [Fintype A]
    (degree : V → ℕ) (fixed : V → Option A)
    (target : A) (z : ℚ) (v : V) : ℚ :=
  match fixed v with
  | some x => if x = target then z ^ degree v else 1
  | none => (Fintype.card A : ℚ) - 1 + z ^ degree v

/--
The vertex sum with independent choices factors for *every* partial
assignment, including assigned and unassigned vertices at once.
-/
theorem conditional_port_factorization
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (degree : V → ℕ) (fixed : V → Option A)
    (target : A) (z : ℚ) :
    (∑ labels ∈ Fintype.piFinset (admissible fixed),
      ∏ v, (if labels v = target then z ^ degree v else (1 : ℚ))) =
      ∏ v, localPortMoment degree fixed target z v := by
  classical
  calc
    _ = ∏ v : V, (∑ label ∈ admissible fixed v,
        if label = target then z ^ degree v else (1 : ℚ)) := by
      rw [Finset.prod_univ_sum]
    _ = ∏ v, localPortMoment degree fixed target z v := by
      apply Finset.prod_congr rfl
      intro v _
      cases h : fixed v with
      | some x =>
          simp [admissible, localPortMoment, h]
      | none =>
          simp only [admissible, localPortMoment, h]
          calc
            (∑ label ∈ (Finset.univ : Finset A),
                if label = target then z ^ degree v else (1 : ℚ)) =
                ∑ label : A, (if label = target then z ^ degree v else (1 : ℚ)) := rfl
            _ = (Fintype.card A : ℚ) - 1 + z ^ degree v := by
              classical
              calc
                _ = ∑ label : A,
                    (1 + (if label = target then z ^ degree v - 1 else 0) : ℚ) := by
                  apply Finset.sum_congr rfl
                  intro label _
                  by_cases he : label = target <;> simp [he]
                _ = (Fintype.card A : ℚ) - 1 + z ^ degree v := by
                  simp [Finset.sum_add_distrib]
                  ring

/-- A source degree-weighted port has the exact sum of whole-vertex powers. -/
theorem conditional_port_power_factorization
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (degree : V → ℕ) (fixed : V → Option A)
    (target : A) (z : ℚ) :
    (∑ labels ∈ Fintype.piFinset (admissible fixed),
      z ^ (∑ v : V,
        if labels v = target then degree v else 0)) =
      ∏ v, localPortMoment degree fixed target z v := by
  classical
  calc
    _ = (∑ labels ∈ Fintype.piFinset (admissible fixed),
        ∏ v, (if labels v = target then z ^ degree v else (1 : ℚ))) := by
      apply Finset.sum_congr rfl
      intro labels _
      have h : (∏ v : V,
          z ^ (if labels v = target then degree v else 0)) =
          z ^ (∑ v : V,
            if labels v = target then degree v else 0) := by
        rw [← Finset.prod_pow_eq_pow_sum]
      rw [← h]
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : labels v = target <;> simp [hv]
    _ = ∏ v, localPortMoment degree fixed target z v :=
      conditional_port_factorization degree fixed target z

/--
For a matching, an edge-local pair-label may have its left endpoint,
right endpoint, both, or neither already committed. The exact
conditional moment factors over those *edge-local* choices.
-/
theorem conditional_matching_pair_factorization
    {E A : Type*} [Fintype E] [DecidableEq E]
    [Fintype A] [DecidableEq A]
    (fixed : E → Option (A × A)) (target : A × A) :
    (∑ labels ∈ Fintype.piFinset (admissible fixed),
      ∏ e, (if labels e = target then (2 : ℚ) else 1)) =
    ∏ e, (∑ label ∈ admissible fixed e,
      if label = target then (2 : ℚ) else 1) := by
  classical
  rw [Finset.prod_univ_sum]

/--
The free vertex-label choice set is finite, and its concrete
cardinality is the product of per-vertex numbers of choices.
-/
theorem conditional_label_space_card
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A]
    (fixed : V → Option A) :
    (Fintype.piFinset (admissible fixed)).card =
      ∏ v, (admissible fixed v).card := by
  classical
  exact Fintype.card_piFinset _

#print axioms TwoAdicConditionalMoments.mem_admissible
#print axioms TwoAdicConditionalMoments.conditional_port_factorization
#print axioms TwoAdicConditionalMoments.conditional_port_power_factorization
#print axioms TwoAdicConditionalMoments.conditional_matching_pair_factorization
#print axioms TwoAdicConditionalMoments.conditional_label_space_card

end TwoAdicConditionalMoments
