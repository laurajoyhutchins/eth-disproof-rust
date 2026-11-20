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


/-! ## Executable, original-source three-state/two-mode fixture -/

/-- A genuine pinned-Anthropic Network with three distinct outgoing
    signatures, and integer weights 1,2,3 at every node. -/
def exampleNetwork : Groundwork.Network (Fin 2) (Fin 3) Bool where
  S := fun _ => Finset.univ
  W := fun _ state =>
    if state = 0 then 1 else if state = 1 then 2 else 3
  Θ := fun _ _ => Finset.univ
  f := fun _ _ state label => ACC.LinearInterface.threeRow state label
  c := fun _ _ => 1

def exampleD (_ _ : Fin 2) : Finset Bool := Finset.univ

def exampleDecode (_ _ : Fin 2) (label : Bool) : Bool := label

/-- Two standard coordinate functions, evaluated at the other node's port. -/
def exampleBasis (mode : Bool) (boundary : Fin 2 → Bool) : ℤ :=
  ACC.LinearInterface.twoBasis mode (boundary 1)

/-- Fully executable exact certificate check across all THREE states and
    all FOUR outside Boolean function assignments. No unsampled context. -/
theorem example_source_table_checked :
    ACC.LinearInterface.Interface.checkFinite
      (exampleNetwork.S 0) (Finset.univ : Finset Bool)
      (Finset.univ : Finset (Fin 2 → Bool))
      (outgoingRow exampleNetwork exampleD exampleDecode 0)
      ACC.LinearInterface.threeCoeff exampleBasis = true := by
  decide

/-- The real pinned Network.toInst for this witness has a two-mode
    circuit-compatible exact decomposition for ALL boundary contexts. -/
theorem example_source_toInst (boundary : Fin 2 → Bool) :
    exampleNetwork.toInst exampleD exampleDecode 0 boundary =
      ∑ mode ∈ (Finset.univ : Finset Bool),
        (∑ state ∈ exampleNetwork.S 0,
          exampleNetwork.W 0 state *
            ACC.LinearInterface.threeCoeff state mode) *
          exampleBasis mode boundary := by
  have hsound : ∀ state ∈ exampleNetwork.S 0, ∀ context,
      outgoingRow exampleNetwork exampleD exampleDecode 0 state context =
        ∑ mode ∈ (Finset.univ : Finset Bool),
          ACC.LinearInterface.threeCoeff state mode *
            exampleBasis mode context := by
    intro state hs context
    exact ACC.LinearInterface.Interface.checkFinite_sound
      (exampleNetwork.S 0) (Finset.univ : Finset Bool)
      (Finset.univ : Finset (Fin 2 → Bool))
      (outgoingRow exampleNetwork exampleD exampleDecode 0)
      ACC.LinearInterface.threeCoeff exampleBasis
      example_source_table_checked state hs context (Finset.mem_univ context)
  exact network_toInst_linear exampleNetwork exampleD exampleDecode 0
    (Finset.univ : Finset Bool)
    ACC.LinearInterface.threeCoeff exampleBasis hsound boundary

/-- Distinct weighted outputs of the original source's explicit network.
    The compressed mode weights here are 1+3=4 and 2+3=5. -/
theorem example_source_false :
    exampleNetwork.toInst exampleD exampleDecode 0 (fun _ => false) = 4 := by
  decide

theorem example_source_true :
    exampleNetwork.toInst exampleD exampleDecode 0 (fun _ => true) = 5 := by
  decide

#print axioms ACC.SourceLinear.example_source_table_checked
#print axioms ACC.SourceLinear.example_source_toInst
#print axioms ACC.SourceLinear.example_source_false
#print axioms ACC.SourceLinear.example_source_true

end ACC.SourceLinear
