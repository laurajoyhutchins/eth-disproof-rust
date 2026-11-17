import Mathlib

/-!
# OpenAI October 25 Cauchy packets preserve contraction at zero

Formalizes the actual cancelled Cauchy polynomial in the October 25, 2026
OpenAI manuscript's appendix ("A Cauchy deformation and integral local
coordinates"), using S = {-L, ..., L-1} and
  W_xy(T) = prod_{q in S, q != y-x} (T-q) / C'(0).

For a source packing, every real edge has a unique (packet, slot) pair;
the same slot is used at both edge endpoints. Empty padded slots have no
ports and therefore contribute no variables to the contraction.

We prove W(0) is the identity on real edges, and then prove that the
manuscript's Boolean interpolation formula F(0) equals the original
finite bipartite contraction for arbitrary surrounding tensors. This
uses no probabilistic independence or special tensor entries.

The proof does not identify an arbitrary Anthropic source network with
the OpenAI source's bipartite network, prove the packet-packing algorithm
constructs a valid packing, or prove precision-dependent recursion.
-/

namespace IndependentETH.OpenAIPackets

open scoped BigOperators

/-- The full set of integer differences from the source appendix. -/
def offsets (L : ℕ) : Finset ℤ :=
  Finset.Icc (-(L : ℤ)) ((L : ℤ) - 1)

private theorem zero_mem_offsets {L : ℕ} (hL : 0 < L) :
    (0 : ℤ) ∈ offsets L := by
  simp only [offsets, Finset.mem_Icc]
  constructor <;> omega

private theorem slot_difference_mem_offsets {L : ℕ} (x y : Fin L) :
    ((y.val : ℤ) - (x.val : ℤ)) ∈ offsets L := by
  simp only [offsets, Finset.mem_Icc]
  have hx := x.isLt
  have hy := y.isLt
  constructor <;> omega

/-- The derivative C'(0) of C(T) = prod_(q in S) (T-q). -/
def cPrimeZero (L : ℕ) : ℚ :=
  ∏ q ∈ (offsets L).erase 0, (-(q : ℚ))

theorem cPrimeZero_ne_zero (L : ℕ) : cPrimeZero L ≠ 0 := by
  unfold cPrimeZero
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  have hne : q ≠ 0 := (Finset.mem_erase.mp hq).1
  have hcast : (q : ℚ) ≠ 0 := by exact_mod_cast hne
  simpa using hcast

/-- The actual source Cauchy polynomial after cancelling T-(y-x).
This form is defined also at T=y-x, unlike a removable rational quotient. -/
def cauchyEntry (L : ℕ) (x y : Fin L) (T : ℚ) : ℚ :=
  (∏ q ∈ (offsets L).erase ((y.val : ℤ) - (x.val : ℤ)),
      (T - (q : ℚ))) / cPrimeZero L

theorem cauchyEntry_zero_diag {L : ℕ} (x : Fin L) :
    cauchyEntry L x x 0 = 1 := by
  unfold cauchyEntry
  rw [sub_self]
  simp only [zero_sub]
  change cPrimeZero L / cPrimeZero L = 1
  exact div_self (cPrimeZero_ne_zero L)

theorem cauchyEntry_zero_offdiag {L : ℕ} (x y : Fin L)
    (hxy : x ≠ y) : cauchyEntry L x y 0 = 0 := by
  have hL : 0 < L := by
    have hx := x.isLt
    omega
  have hd : (y.val : ℤ) - (x.val : ℤ) ≠ 0 := by
    intro h
    have hval : x.val = y.val := by omega
    exact hxy (Fin.ext hval)
  have hm : (0 : ℤ) ∈
      (offsets L).erase ((y.val : ℤ) - (x.val : ℤ)) :=
    Finset.mem_erase.mpr ⟨Ne.symm hd, zero_mem_offsets hL⟩
  have hprod :
      (∏ q ∈ (offsets L).erase ((y.val : ℤ) - (x.val : ℤ)),
        ((0 : ℚ) - (q : ℚ))) = 0 :=
    Finset.prod_eq_zero hm (by simp)
  unfold cauchyEntry
  rw [hprod]
  simp

/-- Source-essential: edge ports have the same slot on both sides,
and every real edge has a distinct packet-slot location. -/
structure ValidPacking (E P : Type*) (L : ℕ) where
  packet : E → P
  slot : E → Fin L
  injective : Function.Injective (fun e => (packet e, slot e))

/-- Off-packet entries vanish, exactly as in the appendix.
Unused padded slots have no corresponding E-index. -/
def packetEntry {E P : Type*} {L : ℕ}
    (packing : ValidPacking E P L) (e f : E) (T : ℚ) : ℚ :=
  if packing.packet e = packing.packet f then
    cauchyEntry L (packing.slot e) (packing.slot f) T
  else 0

/-- The full packed Cauchy matrix, restricted to real ports, is the
identity at T=0. No size or degree bound is needed. -/
theorem packetEntry_zero {E P : Type*} {L : ℕ}
    (packing : ValidPacking E P L) (e f : E) :
    packetEntry packing e f 0 = if e = f then 1 else 0 := by
  classical
  by_cases hp : packing.packet e = packing.packet f
  · by_cases hs : packing.slot e = packing.slot f
    · have he : e = f := packing.injective (Prod.ext hp hs)
      subst f
      simp [packetEntry, cauchyEntry_zero_diag]
    · have he : e ≠ f := by
        intro h
        subst f
        exact hs rfl
      simp [packetEntry, hp, cauchyEntry_zero_offdiag _ _ hs, he]
  · have he : e ≠ f := by
      intro h
      subst f
      exact hp rfl
    simp [packetEntry, hp, he]

/-- Boolean bits embedded in any commutative coefficient ring. -/
def bit {R : Type*} [Semiring R] (b : Bool) : R :=
  if b then 1 else 0

/-- l_0(z)=1-z and l_1(z)=z, as in the source appendix. -/
def interp {R : Type*} [Ring R] (b : Bool) (z : R) : R :=
  if b then z else 1 - z

theorem interp_bit {R : Type*} [Ring R] (x y : Bool) :
    interp y (bit x : R) = if y = x then 1 else 0 := by
  cases x <;> cases y <;> simp [interp, bit]

theorem interpolation_selects_assignment
    {E R : Type*} [Fintype E] [CommRing R]
    (x y : E → Bool) :
    (∏ e : E, interp (y e) (bit (x e) : R)) =
      if y = x then 1 else 0 := by
  classical
  by_cases h : y = x
  · subst y
    have hp (e : E) :
        interp (x e) (bit (x e) : R) = 1 := by
      cases x e <;> simp [interp, bit]
    simp [hp]
  · have he : ∃ e : E, y e ≠ x e := by
      by_contra hn
      apply h
      funext e
      by_contra hne
      exact hn ⟨e, hne⟩
    obtain ⟨e, hne⟩ := he
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    rw [interp_bit]
    simp [hne]

/-- The source's deformed contraction, with real edge assignments
and the original two sets of surrounding row/column tensor factors.
R can be the source's commutative coefficient extension ring. -/
def deformedContraction {E P R : Type*} {L : ℕ}
    [Fintype E] [CommRing R]
    (packing : ValidPacking E P L) (φ : ℚ →+* R)
    (row column : (E → Bool) → R) (T : ℚ) : R :=
  ∑ y : E → Bool, ∑ x : E → Bool,
    row y * column x *
      ∏ e : E, interp (y e)
        (∑ f : E, φ (packetEntry packing e f T) * bit (x f))

/-- The undeformed contraction obtained by identifying the two
endpoint bits of every real edge. -/
def originalContraction {E R : Type*} [Fintype E] [CommRing R]
    (row column : (E → Bool) → R) : R :=
  ∑ x : E → Bool, row x * column x

private theorem packed_linear_zero {E P R : Type*} {L : ℕ}
    [Fintype E] [CommRing R]
    (packing : ValidPacking E P L) (φ : ℚ →+* R)
    (x : E → Bool) (e : E) :
    (∑ f : E, φ (packetEntry packing e f 0) * (bit (x f) : R)) =
      bit (x e) := by
  classical
  calc
    _ = ∑ f : E, (if e = f then (1 : R) else 0) * bit (x f) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [packetEntry_zero]
      split_ifs <;> simp
    _ = bit (x e) := by simp

/-- Source-shaped packet preservation theorem: evaluating the
actual Cauchy-deformed sum at zero gives the original finite
network contraction, for every valid packet/slot assignment. -/
theorem deformedContraction_zero {E P R : Type*} {L : ℕ}
    [Fintype E] [CommRing R]
    (packing : ValidPacking E P L) (φ : ℚ →+* R)
    (row column : (E → Bool) → R) :
    deformedContraction packing φ row column 0 =
      originalContraction row column := by
  classical
  unfold deformedContraction originalContraction
  simp_rw [packed_linear_zero packing φ]
  simp_rw [interpolation_selects_assignment]
  simp

#print axioms IndependentETH.OpenAIPackets.cPrimeZero_ne_zero
#print axioms IndependentETH.OpenAIPackets.packetEntry_zero
#print axioms IndependentETH.OpenAIPackets.interpolation_selects_assignment
#print axioms IndependentETH.OpenAIPackets.deformedContraction_zero

end IndependentETH.OpenAIPackets
