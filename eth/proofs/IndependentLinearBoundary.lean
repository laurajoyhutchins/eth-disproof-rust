import Mathlib
import Groundwork.Net.Net
import ACC.LinearInterface

/-!
# Linear interface adapter for original Anthropic Network.toInst

The source is imported unchanged at the exact pinned Anthropic commit.
The local table is the original product of outgoing half-edge factors.
A certificate decomposes each row over a finite integer basis, including
rows that are different yet linearly dependent.  This yields equality
for ALL outside assignments, even invalid half-edge codes.

This adapter does NOT assert that Anthropic's original merge preserves the
chosen basis dimension. The generic tensor/transfer constructors establish
mathematical closure with explicit mode counts; source-specific efficient
rank preservation through merge remains a separate theorem.
-/

namespace ACC.SourceLinear

open scoped BigOperators

/-- One source state, one outgoing half-edge assignment, and all its
    original factor values, before weighting and summing over states. -/
def outgoingRow
    {J σ τ A : Type*}
    [Fintype J] [LinearOrder J] [DecidableEq A]
    (N : Groundwork.Network J σ τ)
    (D : J → J → Finset A) (decode : J → J → A → τ)
    (a : J) (s : σ) (boundary : J → A) : ℤ :=
  ∏ b ∈ Finset.univ.erase a,
    if boundary b ∈ D (min a b) (max a b) then
      N.f a b s (decode (min a b) (max a b) (boundary b))
    else 0

/-- A source-specific, verified linear decomposition of the entire
    outgoing table. The witness is required on EVERY allowed state and
    EVERY context, rather than just a sampled set of boundaries. -/
def nodeInterface
    {J σ τ A Mode : Type*}
    [Fintype J] [LinearOrder J] [DecidableEq A]
    [DecidableEq σ] [DecidableEq Mode]
    (N : Groundwork.Network J σ τ)
    (D : J → J → Finset A) (decode : J → J → A → τ)
    (a : J)
    (modes : Finset Mode)
    (coeff : σ → Mode → ℤ)
    (basis : Mode → (J → A) → ℤ)
    (hsound : ∀ s ∈ N.S a, ∀ boundary,
      outgoingRow N D decode a s boundary =
        ∑ mode ∈ modes, coeff s mode * basis mode boundary) :
    ACC.LinearInterface.Interface σ Mode (J → A) where
  states := N.S a
  modes := modes
  row := outgoingRow N D decode a
  coeff := coeff
  basis := basis
  reconstruct := hsound

/-- Pinned, source-faithful form of linear boundary compression.
    A table of many distinct rows can be represented by fewer modes,
    with each coefficient weighted and summed exactly. -/
theorem network_toInst_linear
    {J σ τ A Mode : Type*}
    [Fintype J] [LinearOrder J] [DecidableEq A]
    [DecidableEq σ] [DecidableEq Mode]
    (N : Groundwork.Network J σ τ)
    (D : J → J → Finset A) (decode : J → J → A → τ)
    (a : J)
    (modes : Finset Mode)
    (coeff : σ → Mode → ℤ)
    (basis : Mode → (J → A) → ℤ)
    (hsound : ∀ s ∈ N.S a, ∀ boundary,
      outgoingRow N D decode a s boundary =
        ∑ mode ∈ modes, coeff s mode * basis mode boundary)
    (boundary : J → A) :
    N.toInst D decode a boundary =
      ∑ mode ∈ modes,
        (∑ s ∈ N.S a, N.W a s * coeff s mode) *
          basis mode boundary := by
  change
    (∑ s ∈ N.S a, N.W a s * outgoingRow N D decode a s boundary) =
      ∑ mode ∈ modes,
        (∑ s ∈ N.S a, N.W a s * coeff s mode) *
          basis mode boundary
  exact (nodeInterface N D decode a modes coeff basis hsound).weighted_correct
    (N.W a) boundary

#print axioms ACC.SourceLinear.network_toInst_linear

end ACC.SourceLinear
