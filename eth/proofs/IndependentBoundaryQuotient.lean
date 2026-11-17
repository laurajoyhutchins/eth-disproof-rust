import Mathlib
import Groundwork.Net.Net

/-!
# Boundary-state quotient closed under the pinned Anthropic network merge

A compression must preserve an entire boundary function, not just one final
scalar. This module proves such a quotient at EVERY half-edge assignment,
using the actual pinned Network.toInst source declaration.

The soundness hypothesis is *local factor invariance*: f_ab(s, t) depends
on s only through its quotient label. Node weights do NOT need to agree:
they are summed over fibers of that quotient.

Crucially, the original Anthropic Network.merge definition preserves this
factor invariance for the pointwise-lifted quotient. No uniform construction
or good worst-case bound on the number of quotient classes is claimed.
-/

namespace ACC.BoundaryQuotient

open scoped BigOperators

/-- Partition a weighted sum by any finite state-label map.
    Unlike image summation, there is NO injectivity hypothesis. -/
theorem weighted_fiber_sum
    {S K : Type*} [DecidableEq S] [DecidableEq K]
    (states : Finset S) (label : S → K)
    (weight : S → ℤ) (feature : K → ℤ) :
    (∑ s ∈ states, weight s * feature (label s)) =
      ∑ k ∈ states.image label,
        (∑ s ∈ states.filter (fun s => label s = k), weight s) * feature k := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := states) (t := states.image label) (g := label)
    (by intro s hs; exact Finset.mem_image_of_mem label hs)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [(Finset.mem_filter.mp hs).2]

/-- The source's outgoing half-edge product at one node.
    This is the exact factor product appearing inside Network.toInst. -/
noncomputable def nodeBoundary
    {J σ τ A : Type*}
    [Fintype J] [LinearOrder J] [DecidableEq A]
    (N : Groundwork.Network J σ τ)
    (D : J → J → Finset A) (decode : J → J → A → τ)
    (a : J) (s : σ) (boundary : J → A) : ℤ :=
  ∏ b ∈ Finset.univ.erase a,
    if boundary b ∈ D (min a b) (max a b) then
      N.f a b s (decode (min a b) (max a b) (boundary b))
    else 0

/-- Agreement of the original f factors implies agreement at ALL boundary
    assignments, including off-alphabet values mapped to zero. -/
theorem nodeBoundary_invariant
    {J σ τ K A : Type*}
    [Fintype J] [LinearOrder J] [DecidableEq A]
    (N : Groundwork.Network J σ τ)
    (label : σ → K) (representative : K → σ)
    (hf : ∀ a b s t,
      N.f a b s t = N.f a b (representative (label s)) t)
    (D : J → J → Finset A) (decode : J → J → A → τ)
    (a : J) (s : σ) (boundary : J → A) :
    nodeBoundary N D decode a s boundary =
      nodeBoundary N D decode a (representative (label s)) boundary := by
  classical
  unfold nodeBoundary
  apply Finset.prod_congr rfl
  intro b hb
  split_ifs with h
  · exact hf a b s _
  · rfl

/-- Aggregate weights for all original states with the same boundary label.
    No representative state is required to carry the aggregated weight. -/
noncomputable def quotientNode
    {J σ τ K A : Type*}
    [Fintype J] [LinearOrder J] [DecidableEq A]
    (N : Groundwork.Network J σ τ)
    (label : σ → K) (representative : K → σ)
    (D : J → J → Finset A) (decode : J → J → A → τ)
    (a : J) (boundary : J → A) : ℤ := by
  classical
  exact ∑ k ∈ (N.S a).image label,
    (∑ s ∈ (N.S a).filter (fun s => label s = k), N.W a s) *
      nodeBoundary N D decode a (representative k) boundary

/-- Exact SOURCE adapter: each original Anthropic instance table entry is
    computed by the quotient, for every possible external half-edge label
    assignment. This is stronger than preservation of N.value alone. -/
theorem toInst_eq_quotient
    {J σ τ K A : Type*}
    [Fintype J] [LinearOrder J] [DecidableEq A]
    (N : Groundwork.Network J σ τ)
    (label : σ → K) (representative : K → σ)
    (hf : ∀ a b s t,
      N.f a b s t = N.f a b (representative (label s)) t)
    (D : J → J → Finset A) (decode : J → J → A → τ)
    (a : J) (boundary : J → A) :
    N.toInst D decode a boundary =
      quotientNode N label representative D decode a boundary := by
  classical
  change
    (∑ s ∈ N.S a, N.W a s * nodeBoundary N D decode a s boundary) =
      quotientNode N label representative D decode a boundary
  calc
    (∑ s ∈ N.S a, N.W a s * nodeBoundary N D decode a s boundary) =
        ∑ s ∈ N.S a, N.W a s *
          nodeBoundary N D decode a (representative (label s)) boundary := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [nodeBoundary_invariant N label representative hf D decode a s boundary]
    _ = quotientNode N label representative D decode a boundary := by
      exact weighted_fiber_sum (N.S a) label (N.W a)
        (fun k => nodeBoundary N D decode a (representative k) boundary)

/-- The source merge acts on group states coordinatewise. Any globally
    factor-invariant quotient remains factor-invariant after the ACTUAL
    Anthropic Network.merge constructor, for every class and wire label. -/
theorem merge_preserves_factor_invariance
    {J J' σ τ K : Type*}
    [Fintype J] [LinearOrder J] [LinearOrder J']
    (N : Groundwork.Network J σ τ)
    (color : J → J') (defaultState : σ) (defaultLabel : τ)
    (label : σ → K) (representative : K → σ)
    (hf : ∀ a b s t,
      N.f a b s t = N.f a b (representative (label s)) t)
    (G H : J') (z : J → σ) (t : J × J → τ) :
    (N.merge color defaultState defaultLabel).f G H z t =
    (N.merge color defaultState defaultLabel).f G H
      (fun a => representative (label (z a))) t := by
  classical
  change
    (∏ p : J × J with color p.1 = G ∧ color p.2 = H,
      N.f p.1 p.2 (z p.1) (t (if G < H then p else p.swap))) =
    (∏ p : J × J with color p.1 = G ∧ color p.2 = H,
      N.f p.1 p.2 (representative (label (z p.1)))
        (t (if G < H then p else p.swap)))
  apply Finset.prod_congr rfl
  intro p hp
  exact hf p.1 p.2 (z p.1) (t (if G < H then p else p.swap))

/-- A genuinely source-specific commuting square:

    Anthropic MERGE, followed by quotienting each merged group state,
    yields the same entire outgoing instance table as the source MERGE.

    The quotient is lifted pointwise to merged function-valued states.
    In particular, every boundary assignment is covered, not just the
    network's final integer contraction.
-/
theorem merged_toInst_eq_quotient
    {J J' σ τ K A : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    [DecidableEq A]
    (N : Groundwork.Network J σ τ)
    (color : J → J') (defaultState : σ) (defaultLabel : τ)
    (label : σ → K) (representative : K → σ)
    (hf : ∀ a b s t,
      N.f a b s t = N.f a b (representative (label s)) t)
    (D : J' → J' → Finset A)
    (decode : J' → J' → A → (J × J → τ))
    (G : J') (boundary : J' → A) :
    ((N.merge color defaultState defaultLabel).toInst D decode) G boundary =
    quotientNode (N.merge color defaultState defaultLabel)
      (fun z : J → σ => fun a => label (z a))
      (fun k : J → K => fun a => representative (k a))
      D decode G boundary := by
  apply toInst_eq_quotient
  intro X Y z t
  exact merge_preserves_factor_invariance N color defaultState defaultLabel
    label representative hf X Y z t

/-- A right inverse at a single label extends to one on group states.
    Useful for ensuring that a compressed class tag is not lost by lifting. -/
theorem lifted_retraction
    {J σ K : Type*}
    (label : σ → K) (representative : K → σ)
    (hr : ∀ k, label (representative k) = k)
    (z : J → K) :
    (fun a => label (representative (z a))) = z := by
  funext a
  exact hr (z a)

/-- Concrete strict compression: two distinct original states, one label. -/
theorem strict_two_state_compression :
    ((Finset.univ : Finset Bool).image (fun _ => PUnit.unit)).card <
      (Finset.univ : Finset Bool).card := by
  decide

#print axioms ACC.BoundaryQuotient.weighted_fiber_sum
#print axioms ACC.BoundaryQuotient.toInst_eq_quotient
#print axioms ACC.BoundaryQuotient.merge_preserves_factor_invariance
#print axioms ACC.BoundaryQuotient.merged_toInst_eq_quotient
#print axioms ACC.BoundaryQuotient.strict_two_state_compression


/-! ## A real, source-compatible quotient network -/

/-- Construct a new Anthropic network whose node states are quotient labels.
    Node weights are summed over ALL original states in the label fiber.
    Edges still carry the original labels and capacities. -/
noncomputable def quotientNetwork
    {J σ τ K : Type*}
    [Fintype J] [LinearOrder J]
    (N : Groundwork.Network J σ τ)
    (label : σ → K) (representative : K → σ) :
    Groundwork.Network J K τ := by
  classical
  exact {
    S := fun a => (N.S a).image label
    W := fun a k =>
      ∑ s ∈ (N.S a).filter (fun s => label s = k), N.W a s
    Θ := N.Θ
    f := fun a b k t => N.f a b (representative k) t
    c := N.c
  }

/-- Strong source correctness: the constructed quotient network has the
    SAME complete outgoing instance table for every legal or illegal
    external label assignment. No final-count oracle appears. -/
theorem quotientNetwork_toInst
    {J σ τ K A : Type*}
    [Fintype J] [LinearOrder J] [DecidableEq A]
    (N : Groundwork.Network J σ τ)
    (label : σ → K) (representative : K → σ)
    (hf : ∀ a b s t,
      N.f a b s t = N.f a b (representative (label s)) t)
    (D : J → J → Finset A) (decode : J → J → A → τ)
    (a : J) (boundary : J → A) :
    (quotientNetwork N label representative).toInst D decode a boundary =
      N.toInst D decode a boundary := by
  rw [toInst_eq_quotient N label representative hf D decode a boundary]
  rfl

/-- The actual, source-derived merge factors commute *definitionally*
    with the lifted quotient: both routes yield the same outgoing local
    factor function. This is a component of the full network square. -/
theorem quotient_merge_factor_commutes
    {J J' σ τ K : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Groundwork.Network J σ τ)
    (color : J → J') (defaultState : σ) (defaultLabel : τ)
    (label : σ → K) (representative : K → σ)
    (G H : J') (z : J → K) (t : J × J → τ) :
    ((quotientNetwork N label representative).merge color
        (label defaultState) defaultLabel).f G H z t =
      (quotientNetwork
        (N.merge color defaultState defaultLabel)
        (fun x : J → σ => fun a => label (x a))
        (fun k : J → K => fun a => representative (k a))).f G H z t := by
  rfl

/-- The two constructions have identical label universes. -/
theorem quotient_merge_labels_commute
    {J J' σ τ K : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Groundwork.Network J σ τ)
    (color : J → J') (defaultState : σ) (defaultLabel : τ)
    (label : σ → K) (representative : K → σ)
    (G H : J') :
    ((quotientNetwork N label representative).merge color
        (label defaultState) defaultLabel).Θ G H =
      (quotientNetwork
        (N.merge color defaultState defaultLabel)
        (fun x : J → σ => fun a => label (x a))
        (fun k : J → K => fun a => representative (k a))).Θ G H := by
  rfl

/-- Their capacity fields also agree, independently of the quotient. -/
theorem quotient_merge_capacity_commutes
    {J J' σ τ K : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Groundwork.Network J σ τ)
    (color : J → J') (defaultState : σ) (defaultLabel : τ)
    (label : σ → K) (representative : K → σ)
    (G H : J') :
    ((quotientNetwork N label representative).merge color
        (label defaultState) defaultLabel).c G H =
      (quotientNetwork
        (N.merge color defaultState defaultLabel)
        (fun x : J → σ => fun a => label (x a))
        (fun k : J → K => fun a => representative (k a))).c G H := by
  rfl

#print axioms ACC.BoundaryQuotient.quotientNetwork_toInst
#print axioms ACC.BoundaryQuotient.quotient_merge_factor_commutes
#print axioms ACC.BoundaryQuotient.quotient_merge_labels_commute
#print axioms ACC.BoundaryQuotient.quotient_merge_capacity_commutes


/-- Finite-label semantic preservation of a *constructed* quotient network,
    not merely of its proposed table representation. The source's exact
    Z_toInst theorem provides the bridge to the full network contraction. -/
theorem quotientNetwork_value
    {J σ τ K : Type*}
    [Fintype J] [LinearOrder J] [Fintype τ]
    (N : Groundwork.Network J σ τ)
    (label : σ → K) (representative : K → σ)
    (hf : ∀ a b s t,
      N.f a b s t = N.f a b (representative (label s)) t)
    (defaultLabel : τ) :
    (quotientNetwork N label representative).value = N.value := by
  classical
  let Q := quotientNetwork N label representative
  let D : J → J → Finset τ := N.Θ
  let dec : J → J → τ → τ := fun _ _ x => x
  have hcode : ∀ a b, a < b →
      Set.BijOn (dec a b) (D a b) (N.Θ a b) := by
    intro a b hab
    exact ⟨(fun x hx => hx), (fun x hx y hy hxy => hxy),
      (fun x hx => ⟨x, hx, rfl⟩)⟩
  have hinst : Q.toInst D dec = N.toInst D dec := by
    funext a boundary
    exact quotientNetwork_toInst N label representative hf D dec a boundary
  have hN : (N.toInst D dec).Z defaultLabel = N.value :=
    Groundwork.Network.Z_toInst N D dec hcode defaultLabel
  have hQ : (Q.toInst D dec).Z defaultLabel = Q.value := by
    apply Groundwork.Network.Z_toInst
    intro a b hab
    exact hcode a b hab
  calc
    Q.value = (Q.toInst D dec).Z defaultLabel := hQ.symm
    _ = (N.toInst D dec).Z defaultLabel := by rw [hinst]
    _ = N.value := hN

/-- Both paths of the quotient/merge diagram have the same exact full
    scalar network value. This is a value-level square: an isomorphism
    between the intermediate networks is not claimed here. -/
theorem quotient_merge_value_commutes
    {J J' σ τ K : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    [Fintype τ]
    (N : Groundwork.Network J σ τ)
    (color : J → J') (defaultState : σ) (defaultLabel : τ)
    (label : σ → K) (representative : K → σ)
    (hf : ∀ a b s t,
      N.f a b s t = N.f a b (representative (label s)) t) :
    ((quotientNetwork N label representative).merge color
        (label defaultState) defaultLabel).value =
      (quotientNetwork
        (N.merge color defaultState defaultLabel)
        (fun x : J → σ => fun a => label (x a))
        (fun k : J → K => fun a => representative (k a))).value := by
  classical
  calc
    ((quotientNetwork N label representative).merge color
        (label defaultState) defaultLabel).value =
      (quotientNetwork N label representative).value := by
        exact Groundwork.Network.value_merge _ color (label defaultState) defaultLabel
    _ = N.value := quotientNetwork_value N label representative hf defaultLabel
    _ = (N.merge color defaultState defaultLabel).value := by
      exact (Groundwork.Network.value_merge N color defaultState defaultLabel).symm
    _ = (quotientNetwork
          (N.merge color defaultState defaultLabel)
          (fun x : J → σ => fun a => label (x a))
          (fun k : J → K => fun a => representative (k a))).value := by
        symm
        exact quotientNetwork_value
          (N.merge color defaultState defaultLabel)
          (fun x : J → σ => fun a => label (x a))
          (fun k : J → K => fun a => representative (k a))
          (fun a b s t =>
            merge_preserves_factor_invariance
              N color defaultState defaultLabel label representative hf a b s t)
          (fun _ : J × J => defaultLabel)

/-!
Source-level obstruction for the OpenAI appendix's zero-deformation Cauchy
identity W(0) = I. This theorem concerns a *full* identity kernel, and
does not assert that OpenAI's full recursive packet algorithm is such a
simple quotient construction. Other algebraic compressors remain possible.
-/
theorem identity_kernel_forces_injective_labels
    {X K : Type*} [DecidableEq X]
    (label : X → K) (representative : K → X)
    (h : ∀ x y,
      (if x = y then (1 : ℤ) else 0) =
      (if representative (label x) = y then (1 : ℤ) else 0)) :
    Function.Injective label := by
  have hrecover (x : X) : representative (label x) = x := by
    have hx := h x x
    by_contra hne
    simp [hne] at hx
  intro x y hxy
  calc
    x = representative (label x) := (hrecover x).symm
    _ = representative (label y) := by rw [hxy]
    _ = y := hrecover y

#print axioms ACC.BoundaryQuotient.quotientNetwork_value
#print axioms ACC.BoundaryQuotient.quotient_merge_value_commutes
#print axioms ACC.BoundaryQuotient.identity_kernel_forces_injective_labels


/-- The *allowed* merged states agree under the two orders. This is an
    exact image-of-tuples theorem; arbitrary invalid function-valued
    states are not part of the network semantics. -/
theorem quotient_merge_states_commute
    {J J' σ τ K : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Groundwork.Network J σ τ)
    (color : J → J') (defaultState : σ) (defaultLabel : τ)
    (label : σ → K) (representative : K → σ)
    (G : J') :
    ((quotientNetwork N label representative).merge color
      (label defaultState) defaultLabel).S G =
    (quotientNetwork
      (N.merge color defaultState defaultLabel)
      (fun x : J → σ => fun a => label (x a))
      (fun k : J → K => fun a => representative (k a))).S G := by
  classical
  apply Finset.ext
  intro z
  simp only [quotientNetwork, Groundwork.Network.merge]
  change
    (z ∈ Groundwork.tuples (fun a : J => color a = G)
       (fun a => (N.S a).image label) (label defaultState)) ↔
    (z ∈ (Groundwork.tuples (fun a : J => color a = G)
       N.S defaultState).image
         (fun w : J → σ => fun a => label (w a)))
  constructor
  · intro hz
    have hz' := (Groundwork.mem_tuples
      (fun a : J => color a = G) (fun a => (N.S a).image label)
      (label defaultState) z).mp hz
    let w : J → σ := fun a =>
      if ha : color a = G then
        Classical.choose (Finset.mem_image.mp ((hz' a).1 ha))
      else defaultState
    have hw : w ∈ Groundwork.tuples (fun a : J => color a = G)
        N.S defaultState := by
      apply (Groundwork.mem_tuples
        (fun a : J => color a = G) N.S defaultState w).mpr
      intro a
      constructor
      · intro ha
        change (if ha' : color a = G then
          Classical.choose (Finset.mem_image.mp ((hz' a).1 ha')) else
          defaultState) ∈ N.S a
        rw [dif_pos ha]
        exact (Classical.choose_spec
          (Finset.mem_image.mp ((hz' a).1 ha))).1
      · intro ha
        simp [w, ha]
    refine Finset.mem_image.mpr ⟨w, hw, ?_⟩
    funext a
    by_cases ha : color a = G
    · have hh := (Classical.choose_spec
        (Finset.mem_image.mp ((hz' a).1 ha))).2
      simpa [w, ha] using hh
    · have hh := (hz' a).2 ha
      simp [w, ha, hh]
  · intro hz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_image.mp hz
    subst z
    have hw' := (Groundwork.mem_tuples
      (fun a : J => color a = G) N.S defaultState w).mp hw
    apply (Groundwork.mem_tuples
      (fun a : J => color a = G)
      (fun a => (N.S a).image label)
      (label defaultState) (fun a => label (w a))).mpr
    intro a
    constructor
    · intro ha
      exact Finset.mem_image.mpr ⟨w a, (hw' a).1 ha, rfl⟩
    · intro ha
      simp [(hw' a).2 ha]

#print axioms ACC.BoundaryQuotient.quotient_merge_states_commute


/-- An exact fiber-sum product lemma for a group of independent source
    coordinates. The quotient is only required to be constant on each
    *admissible* merged group state, not on arbitrary invalid functions. -/
theorem tuple_fiber_product
    {J S K : Type*}
    [Fintype J] [DecidableEq J] [DecidableEq S] [DecidableEq K]
    (P : J → Prop) [DecidablePred P]
    (states : J → Finset S) (defaultState : S)
    (label : S → K) (z : J → K)
    (hz : ∀ a, ¬ P a → z a = label defaultState)
    (weight : J → S → ℤ) :
    (∑ w ∈ (Groundwork.tuples P states defaultState).filter
        (fun w => (fun a => label (w a)) = z),
        ∏ a with P a, weight a (w a)) =
      ∏ a with P a,
        ∑ s ∈ (states a).filter (fun s => label s = z a), weight a s := by
  classical
  have hfiber :
      (Groundwork.tuples P states defaultState).filter
        (fun w => (fun a => label (w a)) = z) =
      Groundwork.tuples P
        (fun a => (states a).filter (fun s => label s = z a))
        defaultState := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hw, hmap⟩
      have hw' := (Groundwork.mem_tuples P states defaultState w).mp hw
      apply (Groundwork.mem_tuples P
        (fun a => (states a).filter (fun s => label s = z a))
        defaultState w).mpr
      intro a
      constructor
      · intro ha
        exact Finset.mem_filter.mpr ⟨(hw' a).1 ha, congrFun hmap a⟩
      · intro ha
        exact (hw' a).2 ha
    · intro hw
      have hw' := (Groundwork.mem_tuples P
        (fun a => (states a).filter (fun s => label s = z a))
        defaultState w).mp hw
      apply And.intro
      · apply (Groundwork.mem_tuples P states defaultState w).mpr
        intro a
        constructor
        · intro ha
          exact (Finset.mem_filter.mp ((hw' a).1 ha)).1
        · intro ha
          exact (hw' a).2 ha
      · funext a
        by_cases ha : P a
        · exact (Finset.mem_filter.mp ((hw' a).1 ha)).2
        · calc
            label (w a) = label defaultState := by
              rw [(hw' a).2 ha]
            _ = z a := (hz a ha).symm
  rw [hfiber]
  exact Groundwork.sum_tuples_prod P
    (fun a => (states a).filter (fun s => label s = z a))
    defaultState weight

/-- Source pair interactions are also unchanged by replacing each state
    with its quotient representative. This holds for all pair labels. -/
theorem quotient_pair_interaction
    {J σ τ K : Type*} [LinearOrder J]
    (N : Groundwork.Network J σ τ)
    (label : σ → K) (representative : K → σ)
    (hf : ∀ a b s t,
      N.f a b s t = N.f a b (representative (label s)) t)
    (a b : J) (s t : σ) :
    N.Ψ a b s t =
      (quotientNetwork N label representative).Ψ a b
        (label s) (label t) := by
  classical
  change
    (∑ θ ∈ N.Θ (min a b) (max a b),
      N.f a b s θ * N.f b a t θ) =
    (∑ θ ∈ N.Θ (min a b) (max a b),
      N.f a b (representative (label s)) θ *
      N.f b a (representative (label t)) θ)
  apply Finset.sum_congr rfl
  intro θ hθ
  rw [hf a b s θ, hf b a t θ]

#print axioms ACC.BoundaryQuotient.tuple_fiber_product
#print axioms ACC.BoundaryQuotient.quotient_pair_interaction


/-- The merged node-weight tables commute under quotienting on all
    admissible group states. This is the one component that requires
    finite-fiber distributivity, rather than definitional reduction. -/
theorem quotient_merge_weight_on_states
    {J J' σ τ K : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Groundwork.Network J σ τ)
    (color : J → J') (defaultState : σ) (defaultLabel : τ)
    (label : σ → K) (representative : K → σ)
    (hf : ∀ a b s t,
      N.f a b s t = N.f a b (representative (label s)) t)
    (G : J') (z : J → K)
    (hz : z ∈ ((quotientNetwork N label representative).merge color
      (label defaultState) defaultLabel).S G) :
    ((quotientNetwork N label representative).merge color
      (label defaultState) defaultLabel).W G z =
    (quotientNetwork
      (N.merge color defaultState defaultLabel)
      (fun x : J → σ => fun a => label (x a))
      (fun k : J → K => fun a => representative (k a))).W G z := by
  classical
  let P : J → Prop := fun a => color a = G
  let Q : Groundwork.Network J K τ :=
    quotientNetwork N label representative
  let fiber : Finset (J → σ) :=
    (Groundwork.tuples P N.S defaultState).filter
      (fun w => (fun a => label (w a)) = z)
  let interaction : ℤ :=
    ∏ p ∈ Groundwork.pairs J with P p.1 ∧ P p.2,
      Q.Ψ p.1 p.2 (z p.1) (z p.2)
  have hvalid : z ∈ Groundwork.tuples P
      (fun a => (N.S a).image label) (label defaultState) := by
    simpa only [P, Q, quotientNetwork, Groundwork.Network.merge] using hz
  have houtside : ∀ a, ¬ P a → z a = label defaultState := by
    intro a ha
    exact ((Groundwork.mem_tuples P
      (fun a => (N.S a).image label)
      (label defaultState) z).mp hvalid a).2 ha
  have hweights :
      (∑ w ∈ fiber, ∏ a with P a, N.W a (w a)) =
      ∏ a with P a,
        ∑ s ∈ (N.S a).filter (fun s => label s = z a),
          N.W a s := by
    exact tuple_fiber_product P N.S defaultState label z houtside N.W
  have hinteraction (w : J → σ) (hw : w ∈ fiber) :
      (∏ p ∈ Groundwork.pairs J with P p.1 ∧ P p.2,
        N.Ψ p.1 p.2 (w p.1) (w p.2)) = interaction := by
    have hmap : (fun a => label (w a)) = z :=
      (Finset.mem_filter.mp hw).2
    dsimp [interaction]
    apply Finset.prod_congr rfl
    intro p hp
    calc
      N.Ψ p.1 p.2 (w p.1) (w p.2) =
        Q.Ψ p.1 p.2 (label (w p.1)) (label (w p.2)) := by
          exact quotient_pair_interaction N label representative hf
            p.1 p.2 (w p.1) (w p.2)
      _ = Q.Ψ p.1 p.2 (z p.1) (z p.2) := by
        rw [congrFun hmap p.1, congrFun hmap p.2]
  have hsum :
      (∑ w ∈ fiber,
        (∏ a with P a, N.W a (w a)) *
          (∏ p ∈ Groundwork.pairs J with P p.1 ∧ P p.2,
             N.Ψ p.1 p.2 (w p.1) (w p.2))) =
      (∏ a with P a,
        ∑ s ∈ (N.S a).filter (fun s => label s = z a),
          N.W a s) * interaction := by
    calc
      (∑ w ∈ fiber,
        (∏ a with P a, N.W a (w a)) *
          (∏ p ∈ Groundwork.pairs J with P p.1 ∧ P p.2,
             N.Ψ p.1 p.2 (w p.1) (w p.2))) =
        ∑ w ∈ fiber, (∏ a with P a, N.W a (w a)) * interaction := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [hinteraction w hw]
      _ = (∑ w ∈ fiber, ∏ a with P a, N.W a (w a)) *
          interaction := by rw [Finset.sum_mul]
      _ = (∏ a with P a,
          ∑ s ∈ (N.S a).filter (fun s => label s = z a),
            N.W a s) * interaction := by rw [hweights]
  simp only [Q, P, fiber, interaction, quotientNetwork,
    Groundwork.Network.merge] at hsum ⊢
  exact hsum.symm

#print axioms ACC.BoundaryQuotient.quotient_merge_weight_on_states

end ACC.BoundaryQuotient
