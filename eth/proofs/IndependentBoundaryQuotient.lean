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
  rw [Finset.sum_fiberwise_of_maps_to
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

end ACC.BoundaryQuotient
