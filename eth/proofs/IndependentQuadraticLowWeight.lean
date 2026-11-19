import Mathlib

/-!
# Quadratic Boolean functions are determined by Hamming-weight ≤ 2 samples

A Boolean assignment is identified with the finite set of coordinates
on which it equals one. Degree-two squarefree polynomials over ZMod 2
have a constant, independent linear coefficients, and independent
quadratic coefficients only on ordered pairs.

This proves *mathematical* uniqueness of reconstruction from zero,
singleton, and doubleton samples. Native Rust code and its sample-budget
logic require a separate implementation-correspondence proof.
-/

namespace IndependentETH.QuadraticLowWeight

open scoped BigOperators

/-- A squarefree degree-two polynomial with no duplicate pair coefficients. -/
structure Coeff (α : Type*) where
  constant : ZMod 2
  linear : α → ZMod 2
  pair : α → α → ZMod 2

/-- A finite subset is the support of a Boolean assignment. -/
def Coeff.eval {α : Type*} [LinearOrder α]
    (p : Coeff α) (support : Finset α) : ZMod 2 :=
  p.constant + (∑ i ∈ support, p.linear i) +
    (∑ i ∈ support, ∑ j ∈ support,
      if i < j then p.pair i j else 0)

@[simp] theorem eval_empty {α : Type*} [LinearOrder α]
    (p : Coeff α) : p.eval ∅ = p.constant := by
  simp [Coeff.eval]

@[simp] theorem eval_singleton {α : Type*} [LinearOrder α]
    (p : Coeff α) (i : α) : p.eval {i} = p.constant + p.linear i := by
  simp [Coeff.eval]

theorem eval_pair {α : Type*} [LinearOrder α]
    (p : Coeff α) (i j : α) (hij : i < j) :
    p.eval ({i, j} : Finset α) =
      p.constant + p.linear i + p.linear j + p.pair i j := by
  have hne : i ≠ j := ne_of_lt hij
  have hnot : ¬ j < i := not_lt_of_ge (le_of_lt hij)
  simp [Coeff.eval, hne, Ne.symm hne, hij, hnot,
    add_assoc, add_left_comm, add_comm]

theorem linear_from_samples {α : Type*} [LinearOrder α]
    (p : Coeff α) (i : α) :
    p.linear i = p.eval {i} - p.eval ∅ := by
  simp [eval_singleton, eval_empty]

theorem pair_from_samples {α : Type*} [LinearOrder α]
    (p : Coeff α) (i j : α) (hij : i < j) :
    p.pair i j =
      p.eval ({i, j} : Finset α) - p.eval {i} -
        p.eval {j} + p.eval ∅ := by
  rw [eval_pair p i j hij, eval_singleton, eval_singleton, eval_empty]
  ring

/-- Equality at zero, singleton and doubleton supports entails equality
at *every* Boolean assignment, regardless of the number of coordinates. -/
theorem ext_of_low_weight_samples {α : Type*} [LinearOrder α]
    (p q : Coeff α)
    (hzero : p.eval ∅ = q.eval ∅)
    (hone : ∀ i : α, p.eval {i} = q.eval {i})
    (htwo : ∀ i j : α, i < j →
      p.eval ({i, j} : Finset α) = q.eval ({i, j} : Finset α))
    (support : Finset α) :
    p.eval support = q.eval support := by
  have hc : p.constant = q.constant := by
    simpa only [eval_empty] using hzero
  have hl : ∀ i : α, p.linear i = q.linear i := by
    intro i
    rw [linear_from_samples p i, linear_from_samples q i,
      hone i, hzero]
  have hp : ∀ i j : α, i < j → p.pair i j = q.pair i j := by
    intro i j hij
    rw [pair_from_samples p i j hij, pair_from_samples q i j hij,
      htwo i j hij, hone i, hone j, hzero]
  have hlinear :
      (∑ i ∈ support, p.linear i) =
        (∑ i ∈ support, q.linear i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hl i
  have hpairs :
      (∑ i ∈ support, ∑ j ∈ support,
        if i < j then p.pair i j else 0) =
      (∑ i ∈ support, ∑ j ∈ support,
        if i < j then q.pair i j else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i < j
    · simp [h, hp i j h]
    · simp [h]
  unfold Coeff.eval
  rw [hc, hlinear, hpairs]


/-!
## Executable low-weight certificate and signed local witness boundary

This refines the mathematical finite-sample equality test into a Boolean
checker over the exact coefficient type. Its accepted result is an
all-context equality witness. It does NOT prove the native Rust decoder,
allocator, interpolation loop or row interpreter implements this checker.
-/

/-- Executable comparison of all weight-zero, one and two samples.
Finite quantifiers are over Fin n, not the powerset of its assignments. -/
def checkSamples {n : ℕ} (expected claimed : Coeff (Fin n)) : Bool :=
  decide (
    expected.eval ∅ = claimed.eval ∅ ∧
    (∀ i : Fin n, expected.eval {i} = claimed.eval {i}) ∧
    (∀ i j : Fin n, i < j →
      expected.eval ({i, j} : Finset (Fin n)) =
        claimed.eval ({i, j} : Finset (Fin n))))

/-- Acceptance constructs the precise all-boundary equality needed for an
integer-valued local signed-elimination witness. -/
theorem checkSamples_sound {n : ℕ} (expected claimed : Coeff (Fin n))
    (accepted : checkSamples expected claimed = true)
    (support : Finset (Fin n)) :
    expected.eval support = claimed.eval support := by
  have h :
      expected.eval ∅ = claimed.eval ∅ ∧
      (∀ i : Fin n, expected.eval {i} = claimed.eval {i}) ∧
      (∀ i j : Fin n, i < j →
        expected.eval ({i, j} : Finset (Fin n)) =
          claimed.eval ({i, j} : Finset (Fin n))) := by
    simpa only [checkSamples, decide_eq_true_eq] using accepted
  exact ext_of_low_weight_samples expected claimed h.1 h.2.1 h.2.2 support

/-- Every valid coefficient pair passes the executable sample checker. -/
theorem checkSamples_complete {n : ℕ} (p : Coeff (Fin n)) :
    checkSamples p p = true := by
  simp [checkSamples]

/-- Integer semantics of a Boolean sign, distinct from GF(2) arithmetic. -/
def signedBit (phase : Bool) : ℤ := if phase = true then -1 else 1

/-- Read one GF(2) coefficient evaluation as a Boolean phase bit. -/
def phaseBit {n : ℕ} (p : Coeff (Fin n))
    (support : Finset (Fin n)) : Bool :=
  decide (p.eval support = 1)

/-- A checked low-weight certificate also preserves the exact integer sign. -/
theorem checkSamples_sign_sound {n : ℕ}
    (expected claimed : Coeff (Fin n))
    (accepted : checkSamples expected claimed = true)
    (support : Finset (Fin n)) :
    signedBit (phaseBit expected support) =
      signedBit (phaseBit claimed support) := by
  have h := checkSamples_sound expected claimed accepted support
  simp [phaseBit, h]

/-- Algebraic signed cancellation used by the free-variable receipt.
Proof uses all four Boolean cases, not probabilistic sampling. -/
private theorem signedBoolFiber (a ell : Bool) :
    (∑ x : Bool, signedBit (a ^^ (x && ell))) =
      if ell = true then 0 else 2 * signedBit a := by
  cases a <;> cases ell <;> decide

/-- When the source has the stipulated quadratic/affine split, a checked
low-weight phase certificate and the exact cancellation constraint imply
the correct integer-valued free-variable elimination at *every* boundary.

The split hypothesis is a typed source semantic obligation; Rust source-
phase normalization must eventually be proved to instantiate it.
-/
theorem checkedFreeLocalExact {n : ℕ}
    (sourcePhase : Bool → Finset (Fin n) → Bool)
    (expected claimed : Coeff (Fin n))
    (mixed feasible : Finset (Fin n) → Bool)
    (k : ℕ)
    (hsource : ∀ x support,
      sourcePhase x support =
        (phaseBit expected support ^^ (x && mixed support)))
    (accepted : checkSamples expected claimed = true)
    (support : Finset (Fin n)) :
    (∑ x : Bool, if feasible support = true then
       (2 : ℤ) ^ k * signedBit (sourcePhase x support) else 0) =
      (if (feasible support && !(mixed support)) = true then
        (2 : ℤ) ^ (k + 1) * signedBit (phaseBit claimed support)
      else 0) := by
  have hphase : expected.eval support = claimed.eval support :=
    checkSamples_sound expected claimed accepted support
  have hbit : phaseBit expected support = phaseBit claimed support := by
    simp [phaseBit, hphase]
  rw [← hbit]
  simp only [hsource]
  cases hf : feasible support <;>
    cases hm : mixed support <;>
    cases hp : phaseBit expected support <;>
    simp [hf, hm, hp, signedBit, pow_succ] <;> ring

/-- A forced internal variable has exactly one feasible extension. The
checked quadratic phase must match the source at that forced value. -/
theorem checkedForcedLocalExact {n : ℕ}
    (sourcePhase : Bool → Finset (Fin n) → Bool)
    (expected claimed : Coeff (Fin n))
    (forced feasible : Finset (Fin n) → Bool)
    (k : ℕ)
    (hsource : ∀ support,
      sourcePhase (forced support) support = phaseBit expected support)
    (accepted : checkSamples expected claimed = true)
    (support : Finset (Fin n)) :
    (∑ x : Bool, if (x == forced support) && feasible support then
       (2 : ℤ) ^ k * signedBit (sourcePhase x support) else 0) =
      (if feasible support = true then
        (2 : ℤ) ^ k * signedBit (phaseBit claimed support) else 0) := by
  have hphase : expected.eval support = claimed.eval support :=
    checkSamples_sound expected claimed accepted support
  have hbit : phaseBit expected support = phaseBit claimed support := by
    simp [phaseBit, hphase]
  rw [← hbit]
  calc
    (∑ x : Bool, if (x == forced support) && feasible support then
       (2 : ℤ) ^ k * signedBit (sourcePhase x support) else 0) =
        (if feasible support = true then
          (2 : ℤ) ^ k * signedBit (sourcePhase (forced support) support)
        else 0) := by
          cases hf : feasible support <;> cases hx : forced support <;>
            simp [hf, hx, Fintype.sum_bool]
    _ = _ := by rw [hsource support]

#print axioms IndependentETH.QuadraticLowWeight.checkSamples_sound
#print axioms IndependentETH.QuadraticLowWeight.checkSamples_complete
#print axioms IndependentETH.QuadraticLowWeight.checkSamples_sign_sound
#print axioms IndependentETH.QuadraticLowWeight.checkedFreeLocalExact
#print axioms IndependentETH.QuadraticLowWeight.checkedForcedLocalExact

#print axioms IndependentETH.QuadraticLowWeight.eval_pair
#print axioms IndependentETH.QuadraticLowWeight.linear_from_samples
#print axioms IndependentETH.QuadraticLowWeight.pair_from_samples
#print axioms IndependentETH.QuadraticLowWeight.ext_of_low_weight_samples

end IndependentETH.QuadraticLowWeight
