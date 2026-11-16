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
    {E V A : Type*} [Fintype E] [Fintype A] [DecidableEq E] [DecidableEq A]
    (endpoint : E → V) (target : E → A) (v : V) : Finset A := by
  classical
  exact if h : ∃ e : E, endpoint e = v then
    {target (Classical.choose h)}
  else Finset.univ

/-- Each matched vertex has exactly its prescribed label. -/
theorem restrictedLabels_at_endpoint
    {E V A : Type*} [Fintype E] [Fintype A] [DecidableEq E] [DecidableEq A]
    (endpoint : E → V) (target : E → A)
    (hinj : Function.Injective endpoint) (e : E) :
    restrictedLabels endpoint target (endpoint e) = {target e} := by
  classical
  unfold restrictedLabels
  split_ifs with h
  · have he : Classical.choose h = e :=
      hinj (Classical.choose_spec h)
    simpa [he]
  · exact False.elim (h ⟨e, rfl⟩)

/--
Actual source-vertex assignments whose restriction to the matching
edges agrees with a prescribed endpoint label function.
-/
def assignmentFiber
    {E V A : Type*} [Fintype E] [Fintype V] [Fintype A]
    [DecidableEq E] [DecidableEq V] [DecidableEq A]
    (endpoint : E → V) (target : E → A) : Finset (V → A) :=
  (Finset.univ).filter (fun labels => ∀ e : E, labels (endpoint e) = target e)

/--
The actual source vertex-label fiber is a Cartesian product of
one-element matched-vertex label sets and free unmatched-vertex sets.
-/
theorem assignmentFiber_eq_piFinset
    {E V A : Type*} [Fintype E] [Fintype V] [Fintype A]
    [DecidableEq E] [DecidableEq V] [DecidableEq A]
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
    {E V A : Type*} [Fintype E] [Fintype V] [Fintype A]
    [DecidableEq E] [DecidableEq V] [DecidableEq A]
    (endpoint : E → V) (hinj : Function.Injective endpoint)
    (target₁ target₂ : E → A) :
    (assignmentFiber endpoint target₁).card =
      (assignmentFiber endpoint target₂).card := by
  classical
  rw [assignmentFiber_eq_piFinset endpoint target₁ hinj,
    assignmentFiber_eq_piFinset endpoint target₂ hinj]
  rw [Fintype.card_piFinset, Fintype.card_piFinset]
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
    [Fintype E] [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq E] [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (target : E → A × A) : Finset ((L → A) × (R → A)) :=
  (assignmentFiber left (fun e => (target e).1)).product
    (assignmentFiber right (fun e => (target e).2))

theorem bipartiteMatchingFiber_equidistributed
    {E L R A : Type*}
    [Fintype E] [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq E] [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (hl : Function.Injective left)
    (hr : Function.Injective right)
    (target₁ target₂ : E → A × A) :
    (bipartiteMatchingFiber left right target₁).card =
      (bipartiteMatchingFiber left right target₂).card := by
  classical
  simp only [bipartiteMatchingFiber, Finset.product_eq_sprod, Finset.card_product]
  rw [assignmentFiber_equidistributed left hl
        (fun e => (target₁ e).1) (fun e => (target₂ e).1),
    assignmentFiber_equidistributed right hr
        (fun e => (target₁ e).2) (fun e => (target₂ e).2)]

/--
Restrict an actual left/right graph-vertex labeling to the
ordered label pair on each selected matching edge.
-/
def matchingEndpointLabels
    {E L R A : Type*}
    (left : E → L) (right : E → R)
    (vertexLabels : (L → A) × (R → A)) : E → A × A :=
  fun e => (vertexLabels.1 (left e), vertexLabels.2 (right e))

/--
The actual preimage of a matching edge-label assignment is exactly
the Cartesian product of the two source-shore assignment fibers.
-/
theorem matchingEndpointLabels_preimage
    {E L R A : Type*}
    [Fintype E] [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq E] [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (target : E → A × A) :
    ((Finset.univ : Finset ((L → A) × (R → A))).filter
      (fun labels => matchingEndpointLabels left right labels = target)) =
    bipartiteMatchingFiber left right target := by
  classical
  ext labels
  rcases labels with ⟨labL, labR⟩
  change (labL, labR) ∈
      ((Finset.univ : Finset ((L → A) × (R → A))).filter
        (fun labels => matchingEndpointLabels left right labels = target)) ↔
    (labL, labR) ∈
      (assignmentFiber left (fun e => (target e).1)).product
        (assignmentFiber right (fun e => (target e).2))
  constructor
  · intro h
    have hp : matchingEndpointLabels left right (labL, labR) = target :=
      (Finset.mem_filter.mp h).2
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro e
      exact congrArg Prod.fst (congrFun hp e)
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro e
      exact congrArg Prod.snd (congrFun hp e)
  · intro h
    rcases Finset.mem_product.mp h with ⟨hl, hr⟩
    have hL := (Finset.mem_filter.mp hl).2
    have hR := (Finset.mem_filter.mp hr).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    funext e
    exact Prod.ext (hL e) (hR e)

/--
The matching-dependent weighted sum over *every graph vertex-label
assignment* is the edge-local sum multiplied by the common number of
global completions. Thus every edge-pair-label assignment has equal
weight in the source graph's uniform labeling distribution.

In particular, applying this to the exact `2^X_gamma` weight
transfers its previously verified matching-edge moment without
introducing an independence assumption on the other graph edges.
-/
theorem matchingEndpointLabels_weighted_sum
    {E L R A : Type*}
    [Fintype E] [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq E] [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (reference : E → A × A)
    (weight : (E → A × A) → ℚ) :
    (∑ full : (L → A) × (R → A),
      weight (matchingEndpointLabels left right full)) =
    ((bipartiteMatchingFiber left right reference).card : ℚ) *
      (∑ pairs : E → A × A, weight pairs) := by
  classical
  let restrict : ((L → A) × (R → A)) → (E → A × A) :=
    matchingEndpointLabels left right
  have hfiber (pairs : E → A × A) :
      (((Finset.univ : Finset ((L → A) × (R → A))).filter
        (fun full => restrict full = pairs)).card) =
      (bipartiteMatchingFiber left right reference).card := by
    change (((Finset.univ : Finset ((L → A) × (R → A))).filter
      (fun full => matchingEndpointLabels left right full = pairs)).card) =
      (bipartiteMatchingFiber left right reference).card
    rw [matchingEndpointLabels_preimage left right pairs]
    exact bipartiteMatchingFiber_equidistributed left right hl hr pairs reference
  calc
    _ = ∑ pairs : E → A × A,
        ∑ full ∈ (Finset.univ : Finset ((L → A) × (R → A)))
          with restrict full = pairs, weight pairs := by
        symm
        exact Finset.sum_fiberwise' Finset.univ restrict weight
    _ = ∑ pairs : E → A × A,
        (((Finset.univ : Finset ((L → A) × (R → A))).filter
            (fun full => restrict full = pairs)).card : ℚ) * weight pairs := by
        apply Finset.sum_congr rfl
        intro pairs _
        simp
    _ = ∑ pairs : E → A × A,
        ((bipartiteMatchingFiber left right reference).card : ℚ) *
            weight pairs := by
        apply Finset.sum_congr rfl
        intro pairs _
        rw [hfiber pairs]
    _ = ((bipartiteMatchingFiber left right reference).card : ℚ) *
        (∑ pairs : E → A × A, weight pairs) := by
        rw [Finset.mul_sum]

#print axioms TwoAdicMatchingGraph.restrictedLabels_at_endpoint
#print axioms TwoAdicMatchingGraph.assignmentFiber_eq_piFinset
#print axioms TwoAdicMatchingGraph.assignmentFiber_equidistributed
#print axioms TwoAdicMatchingGraph.bipartiteMatchingFiber_equidistributed
#print axioms TwoAdicMatchingGraph.matchingEndpointLabels_preimage
#print axioms TwoAdicMatchingGraph.matchingEndpointLabels_weighted_sum

end TwoAdicMatchingGraph
