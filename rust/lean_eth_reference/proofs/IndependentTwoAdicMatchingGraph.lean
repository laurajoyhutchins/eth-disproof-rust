import Mathlib

/-!
# Uniform matching-endpoint label fibers in an actual bipartite graph

Let `E` index a fixed matching of source edges. For arbitrary finite
left and right vertex types, its endpoint maps `left : E → L` and
`right : E → R` must be injective. No restriction is imposed on
vertices outside the matching; they may have other incident edges.

The finite fiber of any prescribed matching endpoint labels consists
of *all global graph vertex labelings* with those prescribed edge
labels. We prove that all such fibers have the same cardinality,
independently of the prescribed labels. Thus no source edge pair is
privileged by sampling uniform labels on the entire graph.

This uses exact finite combinatorics, not a presumed independence
claim. The source algorithm's packet routing and counting semantics
remain separate.
-/

namespace TwoAdicMatchingGraph

open scoped BigOperators

/--
For a matching's injective endpoint map, choices at a matched
vertex are the one prescribed label; unmatched vertices are free.
-/
noncomputable def restrictedLabels
    {E V A : Type*} [Fintype A] [DecidableEq A]
    (endpoint : E → V) (target : E → A) (v : V) : Finset A :=
  if h : ∃ e : E, endpoint e = v then
    {target (Classical.choose h)}
  else Finset.univ

/-- Each matched vertex has exactly its prescribed label. -/
theorem restrictedLabels_at_endpoint
    {E V A : Type*} [Fintype A] [DecidableEq A]
    (endpoint : E → V) (target : E → A)
    (hinj : Function.Injective endpoint) (e : E) :
    restrictedLabels endpoint target (endpoint e) = {target e} := by
  classical
  unfold restrictedLabels
  simp only [dif_pos (show ∃ x : E, endpoint x = endpoint e from ⟨e, rfl⟩)]
  have hchosen :
      Classical.choose (show ∃ x : E, endpoint x = endpoint e from ⟨e, rfl⟩) = e := by
    apply hinj
    exact Classical.choose_spec
      (show ∃ x : E, endpoint x = endpoint e from ⟨e, rfl⟩)
  rw [hchosen]

/--
Actual source-vertex assignments whose restriction to the matching
edges agrees with a prescribed endpoint label function.
-/
def assignmentFiber
    {E V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (endpoint : E → V) (target : E → A) : Finset (V → A) :=
  (Finset.univ).filter (fun labels => ∀ e : E, labels (endpoint e) = target e)

/--
The actual source vertex-label fiber is a Cartesian product of
one-element matched-vertex label sets and free unmatched-vertex sets.
-/
theorem assignmentFiber_eq_piFinset
    {E V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (endpoint : E → V) (target : E → A)
    (hinj : Function.Injective endpoint) :
    assignmentFiber endpoint target =
      Fintype.piFinset (restrictedLabels endpoint target) := by
  classical
  ext labels
  simp only [assignmentFiber, Finset.mem_filter, Finset.mem_univ,
    true_and, Fintype.mem_piFinset]
  constructor
  · intro h v
    by_cases hv : ∃ e : E, endpoint e = v
    · obtain ⟨e, he⟩ := hv
      subst v
      rw [restrictedLabels_at_endpoint endpoint target hinj e]
      simp [h e]
    · simp [restrictedLabels, hv]
  · intro h e
    have hv := h (endpoint e)
    rw [restrictedLabels_at_endpoint endpoint target hinj e] at hv
    simpa using hv

/--
For a fixed injective matching endpoint map, any two target
assignments have exactly the same number of global completions.
The equality is genuinely about fibers in `V → A`, not about a
separately postulated edge-local independent probability model.
-/
theorem assignmentFiber_equidistributed
    {E V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (endpoint : E → V) (hinj : Function.Injective endpoint)
    (target₁ target₂ : E → A) :
    (assignmentFiber endpoint target₁).card =
      (assignmentFiber endpoint target₂).card := by
  classical
  rw [assignmentFiber_eq_piFinset endpoint target₁ hinj,
    assignmentFiber_eq_piFinset endpoint target₂ hinj]
  rw [Finset.card_piFinset, Finset.card_piFinset]
  apply Finset.prod_congr rfl
  intro v _
  by_cases h : ∃ e : E, endpoint e = v
  · simp [restrictedLabels, h]
  · simp [restrictedLabels, h]

/--
For an actual bipartite graph, the matching endpoints on both shores
can be independently prescribed, and all ordered edge-pair label
assignments have the same number of completions in the *global*
left/right vertex-label space.
-/
def bipartiteMatchingFiber
    {E L R A : Type*}
    [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (target : E → A × A) : Finset ((L → A) × (R → A)) :=
  (assignmentFiber left (fun e => (target e).1)).product
    (assignmentFiber right (fun e => (target e).2))

theorem bipartiteMatchingFiber_equidistributed
    {E L R A : Type*}
    [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (hl : Function.Injective left)
    (hr : Function.Injective right)
    (target₁ target₂ : E → A × A) :
    (bipartiteMatchingFiber left right target₁).card =
      (bipartiteMatchingFiber left right target₂).card := by
  classical
  simp only [bipartiteMatchingFiber, Finset.card_product]
  rw [assignmentFiber_equidistributed left hl
        (fun e => (target₁ e).1) (fun e => (target₂ e).1),
    assignmentFiber_equidistributed right hr
        (fun e => (target₁ e).2) (fun e => (target₂ e).2)]

#print axioms TwoAdicMatchingGraph.restrictedLabels_at_endpoint
#print axioms TwoAdicMatchingGraph.assignmentFiber_eq_piFinset
#print axioms TwoAdicMatchingGraph.assignmentFiber_equidistributed
#print axioms TwoAdicMatchingGraph.bipartiteMatchingFiber_equidistributed

end TwoAdicMatchingGraph
