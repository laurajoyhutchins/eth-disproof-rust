import Mathlib
import Groundwork.Net.Net

/-!
# Packet factors and independent network factors: the normalization boundary

Pinned sources:
* OpenAI, math@4eaee87548250b2682affda7d05d947c05554bae,
  October 25 manuscript, appendix tensor-contraction, equations
  tensor-cauchy, tensor-mode-expansion and tensor-recursion-identity.
* Anthropic, formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5,
  eth/proof/networks/Paper/SecNetworks_DefFactor.lean and
  eth/proof/networks/Groundwork/Net/Net.lean.

The OpenAI packet child is formed by extracting a coefficient of a product
of row-affine factors and multiplying the source-mode powers. Anthropic
factors a pair interaction through a shared finite label. In general those
are different factorizations, and an equality of network values does not
identify the factor tables.

These results establish the canonical finite-label factorization, the
single-slot equality-gate correspondence at OpenAI's T = 0, the gauge
nonuniqueness of factor tables, and a weight-one integral obstruction.
They deliberately do NOT claim a full original-packet/Anthropic adapter
or any asymptotic running-time bound.
-/

namespace IndependentETH.PacketFactorBoundary

open scoped BigOperators

/--
Every finite integer interaction F(x,y) factors through the complete
column-state label set. This is an exact algebraic construction, but its
label set can be exponentially large. It is not Anthropic's quantitative
rank bound.
-/
theorem finite_relation_factors_through_columns
    {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (F : X → Y → ℤ) (x : X) (y : Y) :
    F x y =
      ∑ label : Y, F x label * (if label = y then (1 : ℤ) else 0) := by
  classical
  simp only [mul_ite, mul_one, mul_zero]
  simp

/--
The affine row kernel l_y(x), used by OpenAI at W(0) = I.
For a single occupied slot its value is exactly the equality gate.
-/
def singleSlotRow (y x : Bool) : ℤ :=
  if y then (x.toNat : ℤ) else 1 - (x.toNat : ℤ)

/--
For L = 1 the source packet has S = {-1, 0}, C(T) = (T+1)T and
C'(0) = 1. Therefore the exact deformed kernel W_00(T) = T+1.
This is not a guess about its coefficients: it is the single-slot
specialization of OpenAI's Cauchy formula.
-/
def singleSlotDeformed (T : ℤ) (y x : Bool) : ℤ :=
  let argument := (T + 1) * (x.toNat : ℤ)
  if y then argument else 1 - argument

theorem single_slot_deformation_at_zero (y x : Bool) :
    singleSlotDeformed 0 y x = singleSlotRow y x := by
  cases y <;> cases x <;> decide

/--
A raw deformed packet factor at T = -1 is not the fixed identity
interaction encoded by Anthropic-style edge labels. Equality can only
be sought after the required reconstruction/translation.
-/
theorem deformed_packet_not_pointwise_anthropic_edge :
    singleSlotDeformed (-1) true true ≠
      (∑ label : Bool,
        (if true = label then (1 : ℤ) else 0) *
        (if true = label then (1 : ℤ) else 0)) := by
  decide

/--
At T=0 a single-slot packet has W(0)=1. Its row factor agrees with
the edge interaction obtained by summing Anthropic-style delta factors
over one shared bit. The two delta factors are NOT each equal to the
original singleSlotRow function.
-/
theorem single_slot_interaction_equals_factored_edge
    (y x : Bool) :
    singleSlotRow y x =
      ∑ label : Bool,
        (if y = label then (1 : ℤ) else 0) *
        (if x = label then (1 : ℤ) else 0) := by
  cases y <;> cases x <;> decide

/--
An invertible diagonal sign change on the shared labels preserves a
pair interaction, even though it changes both of the individual factors.
Thus equality of complete interactions never uniquely determines the
constituent factor tables.
-/
theorem pair_factor_sign_gauge
    {Θ : Type*} [Fintype Θ]
    (f g ε : Θ → ℤ) (hε : ∀ θ, ε θ * ε θ = 1) :
    (∑ θ, f θ * g θ) =
      ∑ θ, (ε θ * f θ) * (ε θ * g θ) := by
  classical
  apply Finset.sum_congr rfl
  intro θ _
  calc
    f θ * g θ = (ε θ * ε θ) * (f θ * g θ) := by rw [hε θ, one_mul]
    _ = (ε θ * f θ) * (ε θ * g θ) := by ring

/-- Concrete distinct factor pairs with the same one-label interaction. -/
theorem same_interaction_distinct_factors :
    (1 : ℤ) * 1 = (-1 : ℤ) * (-1) ∧ (1 : ℤ) ≠ -1 := by
  norm_num

/--
Even after summing each group's local states, a group-dependent scalar
twist with product one preserves the product of group factors. Factor
equality is stronger than equality of the assembled contraction.
-/
theorem neutral_group_rescaling
    {G : Type*} [Fintype G]
    {X : G → Type*} [∀ g, Fintype (X g)]
    (entry : (g : G) → X g → ℤ)
    (scale : G → ℤ)
    (hscale : (∏ g, scale g) = 1) :
    (∏ g, ∑ x : X g, scale g * entry g x) =
      ∏ g, ∑ x : X g, entry g x := by
  classical
  calc
    (∏ g, ∑ x : X g, scale g * entry g x) =
        ∏ g, scale g * (∑ x : X g, entry g x) := by
          apply Finset.prod_congr rfl
          intro g _
          rw [Finset.mul_sum]
    _ = (∏ g, scale g) * (∏ g, ∑ x : X g, entry g x) := by
          rw [Finset.prod_mul_distrib]
    _ = _ := by rw [hscale, one_mul]

/--
OpenAI's weight-one packet-mode coefficients are divisible by 2, by the
specific geometric expansion in the manuscript. The signed integer
singlet correction in Anthropic's SWAP = I - vv^T has an entry -1,
which is not of that form.

This refutes the naive INTEGER, weight-preserving, coefficientwise
identification of those two specific kinds of modes. It does not refute
equality after a different change of basis or cancellation of modes.
-/
theorem odd_singlet_not_an_integral_weight_one_packet_coefficient :
    ¬ ∃ coefficient : ℤ, (2 : ℤ) * coefficient = -1 := by
  rintro ⟨coefficient, h⟩
  omega

/-
## Complete finite packet interaction, in Anthropic's original Network type

OpenAI's original (deformed) packet expression for a matrix W is a sum
over independent Boolean assignments Y and X of A(Y)B(X), times one
affine row factor for each row. The integer-valued specialization below
retains every row and every matrix entry, not merely one slot.

Anthropic's exact pinned Groundwork.Network has two node states, shared
edge labels, and pair factors f(row,label) * f(col,label). The following
network uses the *entire* column assignment as the shared label. This
is source-structure preserving for the finite contraction at an integral
packet sample. It is not Anthropic's particular low-rank factorization
and its label cardinality is 2^n.
-/

/-- The source's linear row argument (W X)_i, for integer-valued W. -/
def packetRowArgument {n : ℕ} (W : Fin n → Fin n → ℤ)
    (X : Fin n → Bool) (i : Fin n) : ℤ :=
  ∑ j : Fin n, W i j * (X j).toNat

/-- The complete OpenAI packet row product at a fixed W, Y and X. -/
def packetRowProduct {n : ℕ} (W : Fin n → Fin n → ℤ)
    (Y X : Fin n → Bool) : ℤ :=
  ∏ i : Fin n,
    if Y i then packetRowArgument W X i
    else 1 - packetRowArgument W X i

/-
## The original cancelled Cauchy numerator at the undeformed point

For slot difference d = y-x, the source's Cauchy kernel is the
polynomial with factor (T-d) omitted from C(T), divided by C'(0).
At T=0, C'(0) is the product over all grid points except zero.
These finite rational products are exactly that specialization.
The general T=t+αζ case and 2-adic integrality are not covered.
-/

/-- The exact grid S = {-L, ..., L-1} in the source packet. -/
def cauchyGrid (L : ℕ) : Finset ℤ :=
  Finset.Icc (-(L : ℤ)) ((L : ℤ) - 1)

/-- The source denominator C'(0), written as the product of nonzero roots. -/
def cauchyZeroDenominator (L : ℕ) : ℚ :=
  ∏ q ∈ (cauchyGrid L).erase 0, -(q : ℚ)

/-- The source numerator at T=0 with the difference root omitted. -/
def cauchyZeroNumerator (L : ℕ) (x y : Fin L) : ℚ :=
  ∏ q ∈ (cauchyGrid L).erase ((y.val : ℤ) - (x.val : ℤ)), -(q : ℚ)

/-- Source kernel after cancellation of its difference factor. -/
def cauchyZeroKernel (L : ℕ) (x y : Fin L) : ℚ :=
  cauchyZeroNumerator L x y / cauchyZeroDenominator L

private theorem cauchyGrid_zero_mem (L : ℕ) (hL : 0 < L) :
    (0 : ℤ) ∈ cauchyGrid L := by
  simp only [cauchyGrid, Finset.mem_Icc]
  omega

private theorem cauchyZeroDenominator_ne_zero (L : ℕ) :
    cauchyZeroDenominator L ≠ 0 := by
  classical
  unfold cauchyZeroDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
  have hqr : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  simpa using (neg_ne_zero.mpr hqr)

/--
For *every* packet length and pair of slots, the cancelled Cauchy
formula gives the same Kronecker delta as the undeformed original
edge identification. The source's W(0)=I claim is thereby checked at
the concrete rational numerator/denominator level, not assumed here.
-/
theorem cauchyZeroKernel_eq_delta (L : ℕ) (x y : Fin L) :
    cauchyZeroKernel L x y =
      if x = y then (1 : ℚ) else 0 := by
  classical
  by_cases h : x = y
  · subst y
    have hnum : cauchyZeroNumerator L x x = cauchyZeroDenominator L := by
      simp [cauchyZeroNumerator, cauchyZeroDenominator]
    simp [cauchyZeroKernel, hnum, cauchyZeroDenominator_ne_zero L]
  · have hd : (y.val : ℤ) - (x.val : ℤ) ≠ 0 := by
      intro hz
      have hv : x.val = y.val := by omega
      exact h (Fin.ext hv)
    have hL : 0 < L := by omega
    have hz : (0 : ℤ) ∈
        (cauchyGrid L).erase ((y.val : ℤ) - (x.val : ℤ)) :=
      Finset.mem_erase.mpr ⟨Ne.symm hd, cauchyGrid_zero_mem L hL⟩
    have hnum : cauchyZeroNumerator L x y = 0 := by
      unfold cauchyZeroNumerator
      exact Finset.prod_eq_zero hz (by simp)
    simp [cauchyZeroKernel, hnum, h]

/-- Identity packet matrix sends each column bit to the same row bit. -/
theorem identity_packet_row_argument {n : ℕ} (X : Fin n → Bool) (i : Fin n) :
    packetRowArgument (fun j k => if j = k then (1 : ℤ) else 0) X i =
      (X i).toNat := by
  classical
  simp [packetRowArgument]

/-- Boolean equality is the original affine row factor at W = I. -/
theorem identity_affine_gate (y x : Bool) :
    (if y then (x.toNat : ℤ) else 1 - (x.toNat : ℤ)) =
      if y = x then 1 else 0 := by
  cases y <;> cases x <;> decide

/--
For every packet length, the original W(0) = I specializes the FULL
row product to the equality of complete port assignments. This is
the all-slot counterpart of the original one-slot example.
-/
theorem identity_packet_row_product {n : ℕ}
    (Y X : Fin n → Bool) :
    packetRowProduct (fun i j => if i = j then (1 : ℤ) else 0) Y X =
      if Y = X then 1 else 0 := by
  classical
  simp only [packetRowProduct, identity_packet_row_argument]
  simp_rw [identity_affine_gate]
  by_cases h : Y = X
  · subst X
    simp
  · simp only [h, if_false]
    obtain ⟨i, hi⟩ : ∃ i, Y i ≠ X i := by
      by_contra hnot
      apply h
      funext i
      by_contra hine
      exact hnot ⟨i, hine⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/--
The two independent source assignments are encoded by the two entries
of z : Fin 2 → (Fin n → Bool). The type is equivalent to a pair (Y,X).
-/
def packetContraction {n : ℕ} (W : Fin n → Fin n → ℤ)
    (A B : (Fin n → Bool) → ℤ) : ℤ :=
  ∑ z : Fin 2 → (Fin n → Bool),
    A (z 0) * B (z 1) * packetRowProduct W (z 0) (z 1)

/--
Actual Anthropic Groundwork.Network, not an invented surrogate:
node 0 has row state Y and weight A(Y); node 1 has column state X
and weight B(X). The only shared label is a complete column state θ.
The row-side factor is the entire source packet product at θ;
the column-side factor forces θ = X. Both share the original label.
-/
def packetAsNetwork {n : ℕ} (W : Fin n → Fin n → ℤ)
    (A B : (Fin n → Bool) → ℤ) :
    Groundwork.Network (Fin 2) (Fin n → Bool) (Fin n → Bool) := by
  classical
  exact {
    S := fun _ => Finset.univ
    W := fun side z => if side = 0 then A z else B z
    Θ := fun _ _ => Finset.univ
    f := fun side _ z label =>
      if side = 0 then packetRowProduct W z label
      else if z = label then 1 else 0
    c := fun _ _ => n
  }

/--
The ORIGINAL Anthropic pair-interaction definition reduces exactly to
the FULL OpenAI row-product factor. This holds for arbitrary integer
matrices, arbitrary dimensions, and arbitrary row/column assignments.
-/
theorem packetAsNetwork_pair_interaction
    {n : ℕ} (W : Fin n → Fin n → ℤ)
    (A B : (Fin n → Bool) → ℤ)
    (Y X : Fin n → Bool) :
    (packetAsNetwork W A B).Ψ 0 1 Y X =
      packetRowProduct W Y X := by
  classical
  change
    (∑ label : Fin n → Bool,
      packetRowProduct W Y label *
        (if X = label then (1 : ℤ) else 0)) =
      packetRowProduct W Y X
  simpa only [eq_comm] using
    (finite_relation_factors_through_columns (packetRowProduct W) Y X).symm

/--
For the actual ORIGINAL Anthropic Network.value definition, a network
built from every packet row factor has EXACTLY the original packet
contraction value. No replacement of the row product by a count oracle
or a postulated network-value function occurs here.

The result is exact over integers; a separate source-specific 2-adic
precision/refinement theorem is required for the appendix ring A_p.
-/
theorem packetAsNetwork_value_eq_packetContraction
    {n : ℕ} (W : Fin n → Fin n → ℤ)
    (A B : (Fin n → Bool) → ℤ) :
    (packetAsNetwork W A B).value = packetContraction W A B := by
  classical
  have hstates :
      Fintype.piFinset (packetAsNetwork W A B).S =
        (Finset.univ : Finset (Fin 2 → (Fin n → Bool))) := by
    ext z
    simp [packetAsNetwork]
  have hfin : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have hpairs : Groundwork.pairs (Fin 2) =
      ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2)) := by
    decide
  have hnodes (z : Fin 2 → (Fin n → Bool)) :
      (∏ side : Fin 2, (packetAsNetwork W A B).W side (z side)) =
        A (z 0) * B (z 1) := by
    rw [hfin]
    simp [packetAsNetwork]
  have hedge (z : Fin 2 → (Fin n → Bool)) :
      (∏ pair ∈ Groundwork.pairs (Fin 2),
        (packetAsNetwork W A B).Ψ pair.1 pair.2
          (z pair.1) (z pair.2)) =
        packetRowProduct W (z 0) (z 1) := by
    rw [hpairs]
    simp [packetAsNetwork_pair_interaction]
  unfold Groundwork.Network.value packetContraction
  rw [hstates]
  apply Finset.sum_congr rfl
  intro z _
  rw [hnodes z, hedge z]

#print axioms IndependentETH.PacketFactorBoundary.cauchyZeroKernel_eq_delta
#print axioms IndependentETH.PacketFactorBoundary.identity_packet_row_product
#print axioms IndependentETH.PacketFactorBoundary.packetAsNetwork_pair_interaction
#print axioms IndependentETH.PacketFactorBoundary.packetAsNetwork_value_eq_packetContraction
#print axioms IndependentETH.PacketFactorBoundary.finite_relation_factors_through_columns
#print axioms IndependentETH.PacketFactorBoundary.single_slot_deformation_at_zero
#print axioms IndependentETH.PacketFactorBoundary.deformed_packet_not_pointwise_anthropic_edge
#print axioms IndependentETH.PacketFactorBoundary.single_slot_interaction_equals_factored_edge
#print axioms IndependentETH.PacketFactorBoundary.pair_factor_sign_gauge
#print axioms IndependentETH.PacketFactorBoundary.same_interaction_distinct_factors
#print axioms IndependentETH.PacketFactorBoundary.neutral_group_rescaling
#print axioms IndependentETH.PacketFactorBoundary.odd_singlet_not_an_integral_weight_one_packet_coefficient

end IndependentETH.PacketFactorBoundary
