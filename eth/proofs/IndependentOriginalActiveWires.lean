import Mathlib
import IndependentOriginalSatIncidence

/-!
# No-padding Boolean wire realization of the original SAT network

Every wire here corresponds to an *actual* source consecutive-occurrence
link leaving a cluster and entering a later cluster. The type is a
subtype of (unordered source cluster pair, source literal slot) whose
predicate is the original SatNet.Out.

The source's pair-label alphabet is precisely the Boolean assignment
to those active wires, with false on the inactive slots. We prove an
exact bijection of finite summation domains and preserve the original
integer node weights and endpoint indicator factors under it.

This does not prove that the separately specified OpenAI October 25
CNF-to-tensor constructor produces the same incidence graph.
-/

namespace IndependentETH.OriginalActiveWires

open scoped BigOperators
open Finset
open IndependentETH.SourceIncidence
open IndependentETH.OriginalSatNet

variable (φ : List (List (ℕ × Bool))) (g μ k : ℕ)

abbrev Pair := PairEdge (Fin g)
abbrev Slot := Groundwork.SatNet.Sl μ k

/-- One Boolean wire for every original cross-cluster consecutive
occurrence link. Unused slots are not wires. -/
abbrev ActiveWire :=
  {ps : Pair g × Slot μ k //
    Groundwork.SatNet.Out φ ps.1.val.1 ps.1.val.2 ps.2}

/-- Read the bit of a genuine original source link. -/
def encodeLabels
    (θ : Pair g → Slot μ k → Bool)
    (w : ActiveWire φ g μ k) : Bool :=
  θ w.val.1 w.val.2

/-- Reconstruct the original pair-label word, using false exactly
where the source constructor pads slots without a link. -/
def decodeWires
    (bits : ActiveWire φ g μ k → Bool)
    (p : Pair g) (s : Slot μ k) : Bool :=
  if h : Groundwork.SatNet.Out φ p.val.1 p.val.2 s then
    bits ⟨(p, s), h⟩
  else false

/-- The exact finite source assignment domain, as opposed to
arbitrary or duplicated pair-label assignments. -/
def sourceLabels : Finset (Pair g → Slot μ k → Bool) :=
  Fintype.piFinset (allowedLabels (original φ g μ k))

/-- A source-admissible label word is false outside the actual
consecutive-occurrence links. -/
theorem sourceLabels_support
    (θ : Pair g → Slot μ k → Bool)
    (hθ : θ ∈ sourceLabels φ g μ k)
    (p : Pair g) (s : Slot μ k)
    (hnot : ¬ Groundwork.SatNet.Out φ p.val.1 p.val.2 s) :
    θ p s = false := by
  have hp := (Fintype.mem_piFinset.mp hθ) p
  rw [original_edge_labels] at hp
  exact ((Groundwork.mem_tuples
    (Groundwork.SatNet.Out φ p.val.1 p.val.2)
    (fun _ => Finset.univ) false (θ p)).mp hp s).2 hnot

/-- Every active-wire assignment reconstructs a valid source label,
including the original forced-zero padding. -/
theorem decode_mem_sourceLabels
    (bits : ActiveWire φ g μ k → Bool) :
    decodeWires φ g μ k bits ∈ sourceLabels φ g μ k := by
  apply Fintype.mem_piFinset.mpr
  intro p
  rw [original_edge_labels]
  apply (Groundwork.mem_tuples
    (Groundwork.SatNet.Out φ p.val.1 p.val.2)
    (fun _ => Finset.univ) false (decodeWires φ g μ k bits p)).mpr
  intro s
  constructor
  · intro _
    exact Finset.mem_univ _
  · intro hn
    simp [decodeWires, hn]

/-- No active-wire bit is changed when reconstructing and re-encoding. -/
theorem encode_decode
    (bits : ActiveWire φ g μ k → Bool) :
    encodeLabels φ g μ k (decodeWires φ g μ k bits) = bits := by
  funext w
  have hw : Groundwork.SatNet.Out φ w.val.1.val.1 w.val.1.val.2 w.val.2 :=
    w.property
  simp [encodeLabels, decodeWires, hw]

/-- No source pair-label entry is changed: real bits come from
the corresponding wire; padded positions were already forced false. -/
theorem decode_encode
    (θ : Pair g → Slot μ k → Bool)
    (hθ : θ ∈ sourceLabels φ g μ k) :
    decodeWires φ g μ k (encodeLabels φ g μ k θ) = θ := by
  funext p s
  by_cases hs : Groundwork.SatNet.Out φ p.val.1 p.val.2 s
  · simp [decodeWires, encodeLabels, hs]
  · have hz := sourceLabels_support φ g μ k θ hθ p s hs
    simp [decodeWires, hs, hz]

/-- The source-label-to-actual-wire assignment map is injective
on exactly the original admissible domain, without extra assumptions. -/
theorem encode_injOn :
    Set.InjOn (encodeLabels φ g μ k)
      (sourceLabels φ g μ k) := by
  intro θ hθ θ' hθ' h
  calc
    θ = decodeWires φ g μ k (encodeLabels φ g μ k θ) :=
      (decode_encode φ g μ k θ hθ).symm
    _ = decodeWires φ g μ k (encodeLabels φ g μ k θ') := by rw [h]
    _ = θ' := decode_encode φ g μ k θ' hθ'

/-- All and only assignments to the active original wires occur once:
no normalization, duplication, or absent-label multiplicity. -/
theorem source_image_is_all_wires :
    (sourceLabels φ g μ k).image (encodeLabels φ g μ k) =
      (Finset.univ : Finset (ActiveWire φ g μ k → Bool)) := by
  apply Finset.eq_univ_iff_forall.mpr
  intro bits
  apply Finset.mem_image.mpr
  exact ⟨decodeWires φ g μ k bits,
    decode_mem_sourceLabels φ g μ k bits, encode_decode φ g μ k bits⟩

/-- Reindex an arbitrary integer-valued function of the original
source pair labels by exactly the active literal-test Boolean wires. -/
theorem sum_source_eq_active
    (f : (Pair g → Slot μ k → Bool) → ℤ) :
    (∑ θ ∈ sourceLabels φ g μ k, f θ) =
      ∑ bits : ActiveWire φ g μ k → Bool,
        f (decodeWires φ g μ k bits) := by
  classical
  calc
    _ = ∑ bits ∈ (sourceLabels φ g μ k).image (encodeLabels φ g μ k),
          f (decodeWires φ g μ k bits) := by
      rw [Finset.sum_image (encode_injOn φ g μ k)]
      apply Finset.sum_congr rfl
      intro θ hθ
      rw [decode_encode φ g μ k θ hθ]
    _ = _ := by rw [source_image_is_all_wires]

/-- Original source finite-network contraction rewritten over precisely
the active Boolean wires, with source weights and both endpoint factors. -/
def activeWireValue : ℤ :=
  let N := original φ g μ k
  ∑ z ∈ Fintype.piFinset N.S,
    ∑ bits : ActiveWire φ g μ k → Bool,
      (∏ a, N.W a (z a)) *
        (∏ p : Pair g,
          firstFactor N z (decodeWires φ g μ k bits) p *
          secondFactor N z (decodeWires φ g μ k bits) p)

/-- An exact source-derived incidence-preserving, factor-preserving
translation of the ORIGINAL Anthropic SAT constructor into one wire
per actual cross-cluster equality test. -/
theorem original_value_eq_active_wires :
    (original φ g μ k).value = activeWireValue φ g μ k := by
  rw [original_value_eq_incidence]
  unfold incidenceValue activeWireValue
  apply Finset.sum_congr rfl
  intro z hz
  exact sum_source_eq_active φ g μ k _

#print axioms IndependentETH.OriginalActiveWires.source_image_is_all_wires
#print axioms IndependentETH.OriginalActiveWires.sum_source_eq_active
#print axioms IndependentETH.OriginalActiveWires.original_value_eq_active_wires

end IndependentETH.OriginalActiveWires
