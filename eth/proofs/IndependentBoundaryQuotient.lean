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
        apply quotientNetwork_value
        intro a b s t
        exact merge_preserves_factor_invariance
          N color defaultState defaultLabel label representative hf a b s t

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

end ACC.BoundaryQuotient
