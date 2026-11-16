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

/--
Cross-multiplied equality of the **uniform** mean over all graph
vertex labelings and the uniform mean over all matching edge-pair
labels. It holds even at empty finite-alphabet boundary cases,
without requiring division by a possibly zero cardinality.

When the alphabet is nonempty, both denominators are positive,
so this gives equality of the two rational expectations directly.
-/
theorem matchingEndpointLabels_uniform_mean_cross_mul
    {E L R A : Type*}
    [Fintype E] [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq E] [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (reference : E → A × A)
    (weight : (E → A × A) → ℚ) :
    (∑ full : (L → A) × (R → A),
      weight (matchingEndpointLabels left right full)) *
        (Fintype.card (E → A × A) : ℚ) =
    (∑ pairs : E → A × A, weight pairs) *
        (Fintype.card ((L → A) × (R → A)) : ℚ) := by
  classical
  have htotal := matchingEndpointLabels_weighted_sum
    left right hl hr reference weight
  have hone := matchingEndpointLabels_weighted_sum
    left right hl hr reference (fun _ => (1 : ℚ))
  have hcard :
      (Fintype.card ((L → A) × (R → A)) : ℚ) =
        ((bipartiteMatchingFiber left right reference).card : ℚ) *
          (Fintype.card (E → A × A) : ℚ) := by
    simpa using hone
  rw [htotal, hcard]
  ring

/-
The following partial-assignment lemmas use vertex-specific *finite*
sets of allowed symbols. For the source's partial labels, each is
either the entire alphabet or a singleton, but the result holds for
arbitrary finite allowed sets, including an empty set.
-/

/-- Full vertex assignments realizing a matching label, constrained by
an arbitrary allowed-set function at *every* vertex. -/
def conditionalAssignmentFiber
    {E V A : Type*} [Fintype E] [Fintype V] [Fintype A]
    [DecidableEq E] [DecidableEq V] [DecidableEq A]
    (endpoint : E → V) (target : E → A)
    (allowed : V → Finset A) : Finset (V → A) :=
  assignmentFiber endpoint target ∩ Fintype.piFinset allowed

/-- Endpoint constraints and vertex allowed sets combine independently. -/
theorem conditionalAssignmentFiber_eq_piFinset
    {E V A : Type*} [Fintype E] [Fintype V] [Fintype A]
    [DecidableEq E] [DecidableEq V] [DecidableEq A]
    (endpoint : E → V) (target : E → A)
    (allowed : V → Finset A)
    (hinj : Function.Injective endpoint) :
    conditionalAssignmentFiber endpoint target allowed =
      Fintype.piFinset
        (fun v => restrictedLabels endpoint target v ∩ allowed v) := by
  classical
  unfold conditionalAssignmentFiber
  rw [assignmentFiber_eq_piFinset endpoint target hinj]
  ext labels
  simp only [Finset.mem_inter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h₁, h₂⟩ v
    exact ⟨h₁ v, h₂ v⟩
  · intro h
    exact ⟨fun v => (h v).1, fun v => (h v).2⟩

/-- Number of ways to label all vertices *outside* the matching.
Every matched vertex has exactly one allowed value after prescribing
its edge label, so the count does not depend on the prescribed label. -/
noncomputable def unmatchedCompletionCount
    {E V A : Type*} [Fintype E] [Fintype V] [Fintype A]
    [DecidableEq E] [DecidableEq V] [DecidableEq A]
    (endpoint : E → V) (allowed : V → Finset A) : ℕ := by
  classical
  exact ∏ v, if ∃ e : E, endpoint e = v then 1 else (allowed v).card

/-- Any compatible matching-edge labeling has the same exact number
of full vertex-label completions, even after arbitrary vertices have
already been fixed to allowed singleton values. -/
theorem conditionalAssignmentFiber_card
    {E V A : Type*} [Fintype E] [Fintype V] [Fintype A]
    [DecidableEq E] [DecidableEq V] [DecidableEq A]
    (endpoint : E → V) (target : E → A)
    (allowed : V → Finset A)
    (hinj : Function.Injective endpoint)
    (hallowed : ∀ e, target e ∈ allowed (endpoint e)) :
    (conditionalAssignmentFiber endpoint target allowed).card =
      unmatchedCompletionCount endpoint allowed := by
  classical
  rw [conditionalAssignmentFiber_eq_piFinset endpoint target allowed hinj,
    Fintype.card_piFinset]
  unfold unmatchedCompletionCount
  apply Finset.prod_congr rfl
  intro v _
  by_cases hv : ∃ e : E, endpoint e = v
  · obtain ⟨e, he⟩ := hv
    subst v
    rw [restrictedLabels_at_endpoint endpoint target hinj e]
    simp [hallowed e]
  · simp [restrictedLabels, hv]

/-- Two matching assignments compatible with the same partial vertex
constraints have equal numbers of completions. -/
theorem conditionalAssignmentFiber_equidistributed
    {E V A : Type*} [Fintype E] [Fintype V] [Fintype A]
    [DecidableEq E] [DecidableEq V] [DecidableEq A]
    (endpoint : E → V) (allowed : V → Finset A)
    (hinj : Function.Injective endpoint)
    (target₁ target₂ : E → A)
    (h₁ : ∀ e, target₁ e ∈ allowed (endpoint e))
    (h₂ : ∀ e, target₂ e ∈ allowed (endpoint e)) :
    (conditionalAssignmentFiber endpoint target₁ allowed).card =
      (conditionalAssignmentFiber endpoint target₂ allowed).card := by
  rw [conditionalAssignmentFiber_card endpoint target₁ allowed hinj h₁,
    conditionalAssignmentFiber_card endpoint target₂ allowed hinj h₂]

/-- Allowed full graph labels on each shore, under an arbitrary
partial assignment or other vertex-specific finite constraints. -/
def bipartiteAllowedLabelings
    {L R A : Type*} [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (allowedL : L → Finset A) (allowedR : R → Finset A) :
    Finset ((L → A) × (R → A)) :=
  (Fintype.piFinset allowedL).product (Fintype.piFinset allowedR)

/-- A source matching edge receives an ordered pair consisting of
an allowed symbol at each of its left/right endpoints. -/
def matchingPairChoices
    {E L R A : Type*} [Fintype A] [DecidableEq A]
    (left : E → L) (right : E → R)
    (allowedL : L → Finset A) (allowedR : R → Finset A)
    (e : E) : Finset (A × A) :=
  (allowedL (left e)).product (allowedR (right e))

/-- The compatible fiber of a prescribed pair of matching endpoint
labels, with all other graph-vertex assignments still constrained. -/
def conditionalBipartiteMatchingFiber
    {E L R A : Type*}
    [Fintype E] [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq E] [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (allowedL : L → Finset A) (allowedR : R → Finset A)
    (target : E → A × A) : Finset ((L → A) × (R → A)) :=
  (conditionalAssignmentFiber left (fun e => (target e).1) allowedL).product
    (conditionalAssignmentFiber right (fun e => (target e).2) allowedR)

/-- The real graph-vertex matching restriction fiber is precisely
the product of the two source-shore conditional fibers. -/
theorem matchingEndpointLabels_conditional_preimage
    {E L R A : Type*}
    [Fintype E] [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq E] [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (allowedL : L → Finset A) (allowedR : R → Finset A)
    (target : E → A × A) :
    (bipartiteAllowedLabelings allowedL allowedR).filter
      (fun full => matchingEndpointLabels left right full = target) =
    conditionalBipartiteMatchingFiber left right allowedL allowedR target := by
  classical
  ext full
  rcases full with ⟨labL, labR⟩
  change ((labL, labR) ∈
      ((Fintype.piFinset allowedL).product
        (Fintype.piFinset allowedR)).filter
        (fun full => matchingEndpointLabels left right full = target)) ↔
    ((labL, labR) ∈
      (conditionalAssignmentFiber left
        (fun e => (target e).1) allowedL).product
      (conditionalAssignmentFiber right
        (fun e => (target e).2) allowedR))
  constructor
  · intro h
    obtain ⟨hfull, hmatch⟩ := Finset.mem_filter.mp h
    obtain ⟨hL, hR⟩ := Finset.mem_product.mp hfull
    have heqL : ∀ e, labL (left e) = (target e).1 := by
      intro e
      exact congrArg Prod.fst (congrFun hmatch e)
    have heqR : ∀ e, labR (right e) = (target e).2 := by
      intro e
      exact congrArg Prod.snd (congrFun hmatch e)
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqL⟩, hL⟩,
      Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqR⟩, hR⟩⟩
  · intro h
    obtain ⟨hLeft, hRight⟩ := Finset.mem_product.mp h
    obtain ⟨hMatchL, hL⟩ := Finset.mem_inter.mp hLeft
    obtain ⟨hMatchR, hR⟩ := Finset.mem_inter.mp hRight
    have heqL := (Finset.mem_filter.mp hMatchL).2
    have heqR := (Finset.mem_filter.mp hMatchR).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hL, hR⟩, ?_⟩
    funext e
    exact Prod.ext (heqL e) (heqR e)

/-- Every compatible source matching-pair assignment has the same
number of full graph-vertex completions after arbitrary vertex
constraints; the unmatched vertices contribute their allowed-set
cardinalities, independently on each shore. -/
theorem conditionalBipartiteMatchingFiber_card
    {E L R A : Type*}
    [Fintype E] [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq E] [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (allowedL : L → Finset A) (allowedR : R → Finset A)
    (target : E → A × A)
    (hcompatible : ∀ e, target e ∈
      matchingPairChoices left right allowedL allowedR e) :
    (conditionalBipartiteMatchingFiber
      left right allowedL allowedR target).card =
      unmatchedCompletionCount left allowedL *
        unmatchedCompletionCount right allowedR := by
  classical
  have hL (e : E) : (target e).1 ∈ allowedL (left e) :=
    (Finset.mem_product.mp (hcompatible e)).1
  have hR (e : E) : (target e).2 ∈ allowedR (right e) :=
    (Finset.mem_product.mp (hcompatible e)).2
  simp only [conditionalBipartiteMatchingFiber,
    Finset.product_eq_sprod, Finset.card_product]
  rw [conditionalAssignmentFiber_card left
      (fun e => (target e).1) allowedL hl hL,
    conditionalAssignmentFiber_card right
      (fun e => (target e).2) allowedR hr hR]

/-- Conditional matching-edge weighted-sum transfer. All vertices
have arbitrary finite allowed symbol sets. The equal-fiber factor
counts the choices at vertices *not in the selected matching*,
whereas the edge-local sum ranges only over label pairs compatible
with every endpoint's allowed set.

The result applies to **any** rational matching-dependent weight,
not just a chosen exponential collision observable. -/
theorem matchingEndpointLabels_conditional_weighted_sum
    {E L R A : Type*}
    [Fintype E] [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq E] [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (allowedL : L → Finset A) (allowedR : R → Finset A)
    (weight : (E → A × A) → ℚ) :
    (∑ full ∈ bipartiteAllowedLabelings allowedL allowedR,
      weight (matchingEndpointLabels left right full)) =
    ((unmatchedCompletionCount left allowedL *
        unmatchedCompletionCount right allowedR : ℕ) : ℚ) *
      (∑ pairs ∈ Fintype.piFinset
          (matchingPairChoices left right allowedL allowedR),
        weight pairs) := by
  classical
  let fulls : Finset ((L → A) × (R → A)) :=
    bipartiteAllowedLabelings allowedL allowedR
  let pairs : Finset (E → A × A) :=
    Fintype.piFinset (matchingPairChoices left right allowedL allowedR)
  let restrict : ((L → A) × (R → A)) → (E → A × A) :=
    matchingEndpointLabels left right
  let c : ℚ := ((unmatchedCompletionCount left allowedL *
    unmatchedCompletionCount right allowedR : ℕ) : ℚ)
  have hsource (full : (L → A) × (R → A)) (hf : full ∈ fulls) :
      restrict full ∈ pairs := by
    rcases full with ⟨labL, labR⟩
    have hfull : (labL, labR) ∈
        (Fintype.piFinset allowedL).product
          (Fintype.piFinset allowedR) := hf
    rcases Finset.mem_product.mp hfull with ⟨hL, hR⟩
    apply Fintype.mem_piFinset.mpr
    intro e
    apply Finset.mem_product.mpr
    exact ⟨(Fintype.mem_piFinset.mp hL) (left e),
      (Fintype.mem_piFinset.mp hR) (right e)⟩
  have hcount (p : E → A × A) (hp : p ∈ pairs) :
      ((fulls.filter (fun full => restrict full = p)).card : ℚ) = c := by
    have hcompat (e : E) : p e ∈
        matchingPairChoices left right allowedL allowedR e :=
      (Fintype.mem_piFinset.mp hp) e
    dsimp only [fulls, restrict, c]
    rw [matchingEndpointLabels_conditional_preimage left right allowedL allowedR p,
      conditionalBipartiteMatchingFiber_card
        left right hl hr allowedL allowedR p hcompat]
  have hzero (p : E → A × A) (hp : p ∉ pairs) :
      ((fulls.filter (fun full => restrict full = p)).card : ℚ) = 0 := by
    have he : fulls.filter (fun full => restrict full = p) = ∅ := by
      ext full
      constructor
      · intro hf
        obtain ⟨hfull, heq⟩ := Finset.mem_filter.mp hf
        exact False.elim (hp (by simpa [heq] using hsource full hfull))
      · simp
    simp [he]
  calc
    _ = ∑ p : E → A × A,
        ∑ full ∈ fulls with restrict full = p, weight p := by
      symm
      exact Finset.sum_fiberwise' fulls restrict weight
    _ = ∑ p : E → A × A,
        (((fulls.filter (fun full => restrict full = p)).card : ℚ) *
          weight p) := by
      apply Finset.sum_congr rfl
      intro p _
      simp
    _ = ∑ p : E → A × A, if p ∈ pairs then c * weight p else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      split_ifs with hp
      · rw [hcount p hp]
      · rw [hzero p hp]
        ring
    _ = ∑ p ∈ pairs, c * weight p := by
      simp [Finset.sum_filter]
    _ = c * (∑ p ∈ pairs, weight p) := by
      rw [Finset.mul_sum]

/-- Specialization of the conditional source-graph weighted transfer
to the actual exponential load of a chosen ordered label class.
The remaining edge-local sum factors by independent matching edges,
because the *matching endpoint maps* were proved injective. -/
theorem matchingEndpointLabels_conditional_class_moment
    {E L R A : Type*}
    [Fintype E] [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq E] [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (allowedL : L → Finset A) (allowedR : R → Finset A)
    (target : A × A) :
    (∑ full ∈ bipartiteAllowedLabelings allowedL allowedR,
      (2 : ℚ) ^ (∑ e : E,
        if matchingEndpointLabels left right full e = target then 1 else 0)) =
    ((unmatchedCompletionCount left allowedL *
        unmatchedCompletionCount right allowedR : ℕ) : ℚ) *
      (∏ e : E,
        (∑ pair ∈ matchingPairChoices left right allowedL allowedR e,
          if pair = target then (2 : ℚ) else 1)) := by
  classical
  calc
    _ = (∑ full ∈ bipartiteAllowedLabelings allowedL allowedR,
      ∏ e, (if matchingEndpointLabels left right full e = target
        then (2 : ℚ) else 1)) := by
      apply Finset.sum_congr rfl
      intro full _
      have hf : (2 : ℚ) ^ (∑ e : E,
          if matchingEndpointLabels left right full e = target then 1 else 0) =
          ∏ e : E, (if matchingEndpointLabels left right full e = target
            then (2 : ℚ) else 1) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_congr rfl
        intro e _
        by_cases he : matchingEndpointLabels left right full e = target <;>
          simp [he]
      exact hf
    _ = ((unmatchedCompletionCount left allowedL *
        unmatchedCompletionCount right allowedR : ℕ) : ℚ) *
        (∑ pairs ∈ Fintype.piFinset
            (matchingPairChoices left right allowedL allowedR),
          ∏ e, (if pairs e = target then (2 : ℚ) else 1)) :=
      matchingEndpointLabels_conditional_weighted_sum
        left right hl hr allowedL allowedR
        (fun pairs => ∏ e, if pairs e = target then (2 : ℚ) else 1)
    _ = ((unmatchedCompletionCount left allowedL *
        unmatchedCompletionCount right allowedR : ℕ) : ℚ) *
        (∏ e : E, ∑ pair ∈ matchingPairChoices left right allowedL allowedR e,
          if pair = target then (2 : ℚ) else 1) := by
      rw [Finset.prod_univ_sum]

/-- The uniform conditional mean over the **actual source graph
vertex** completions agrees exactly with the uniform conditional mean
over the independent, endpoint-compatible matching-edge pair choices.
Cross multiplication avoids dividing by zero when a partial constraint
makes the completion space empty.

The theorem holds for every rational matching-dependent weight,
including `2^X_gamma`, and for any finite allowable symbols per vertex.
-/
theorem matchingEndpointLabels_conditional_uniform_mean_cross_mul
    {E L R A : Type*}
    [Fintype E] [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq E] [DecidableEq L] [DecidableEq R] [DecidableEq A]
    (left : E → L) (right : E → R)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (allowedL : L → Finset A) (allowedR : R → Finset A)
    (weight : (E → A × A) → ℚ) :
    (∑ full ∈ bipartiteAllowedLabelings allowedL allowedR,
      weight (matchingEndpointLabels left right full)) *
        ((Fintype.piFinset
          (matchingPairChoices left right allowedL allowedR)).card : ℚ) =
    (∑ pairs ∈ Fintype.piFinset
        (matchingPairChoices left right allowedL allowedR),
        weight pairs) *
      ((bipartiteAllowedLabelings allowedL allowedR).card : ℚ) := by
  classical
  have hweight := matchingEndpointLabels_conditional_weighted_sum
    left right hl hr allowedL allowedR weight
  have hone := matchingEndpointLabels_conditional_weighted_sum
    left right hl hr allowedL allowedR (fun _ => (1 : ℚ))
  have hcard :
      ((bipartiteAllowedLabelings allowedL allowedR).card : ℚ) =
      ((unmatchedCompletionCount left allowedL *
        unmatchedCompletionCount right allowedR : ℕ) : ℚ) *
      ((Fintype.piFinset
        (matchingPairChoices left right allowedL allowedR)).card : ℚ) := by
    simpa using hone
  rw [hweight, hcard]
  ring

#print axioms TwoAdicMatchingGraph.restrictedLabels_at_endpoint
#print axioms TwoAdicMatchingGraph.assignmentFiber_eq_piFinset
#print axioms TwoAdicMatchingGraph.assignmentFiber_equidistributed
#print axioms TwoAdicMatchingGraph.bipartiteMatchingFiber_equidistributed
#print axioms TwoAdicMatchingGraph.matchingEndpointLabels_preimage
#print axioms TwoAdicMatchingGraph.matchingEndpointLabels_weighted_sum
#print axioms TwoAdicMatchingGraph.matchingEndpointLabels_uniform_mean_cross_mul
#print axioms TwoAdicMatchingGraph.conditionalAssignmentFiber_eq_piFinset
#print axioms TwoAdicMatchingGraph.conditionalAssignmentFiber_card
#print axioms TwoAdicMatchingGraph.conditionalAssignmentFiber_equidistributed
#print axioms TwoAdicMatchingGraph.matchingEndpointLabels_conditional_preimage
#print axioms TwoAdicMatchingGraph.conditionalBipartiteMatchingFiber_card
#print axioms TwoAdicMatchingGraph.matchingEndpointLabels_conditional_weighted_sum
#print axioms TwoAdicMatchingGraph.matchingEndpointLabels_conditional_class_moment
#print axioms TwoAdicMatchingGraph.matchingEndpointLabels_conditional_uniform_mean_cross_mul

end TwoAdicMatchingGraph
