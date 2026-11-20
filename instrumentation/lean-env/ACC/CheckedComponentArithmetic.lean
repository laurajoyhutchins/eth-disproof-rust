import Mathlib
import ACC.IndexedRankedCertificate

/-!
# Exactness of bounded checked component arithmetic

An executable-looking reference model uses Option to represent failure of
signed 128-bit bounds checks. Its successful branch performs ordinary integer
arithmetic; it never wraps, saturates, or loses sign. The proof covers an
arbitrary ordered list of per-component unary-weight lists, in the same
0-choice/1-choice arrangement used by the Rust contraction.

This proves a *Lean arithmetic interpreter* is sound conditional on success.
It does not yet prove the Rust i128 machine operations implement the Lean
checks, nor that the Rust grouping loops construct the same lists.
-/

namespace ACC.CheckedComponentArithmetic

/-- Signed 128-bit mathematical range, including the asymmetric minimum. -/
def WithinI128 (z : ℤ) : Prop :=
  -(2 ^ 127 : ℤ) ≤ z ∧ z < (2 ^ 127 : ℤ)

/-- Constructive comparison on mathematical integers; executable in Lean. -/
instance instDecidableWithinI128 (z : ℤ) : Decidable (WithinI128 z) := by
  dsimp [WithinI128]
  infer_instance

def checkedMul (a b : ℤ) : Option ℤ :=
  if WithinI128 (a * b) then some (a * b) else none

def checkedAdd (a b : ℤ) : Option ℤ :=
  if WithinI128 (a + b) then some (a + b) else none

theorem checkedMul_some {a b z : ℤ}
    (h : checkedMul a b = some z) : z = a * b := by
  unfold checkedMul at h
  split_ifs at h with hb
  · exact (Option.some.inj h).symm

theorem checkedAdd_some {a b z : ℤ}
    (h : checkedAdd a b = some z) : z = a + b := by
  unfold checkedAdd at h
  split_ifs at h with hb
  · exact (Option.some.inj h).symm

/-- Sequential checked multiplication with an explicit initial accumulator. -/
def checkedProductFrom (acc : ℤ) : List ℤ → Option ℤ
  | [] => some acc
  | x :: xs =>
      (checkedMul acc x).bind (fun next => checkedProductFrom next xs)

/-- Every successful checked product equals the exact full integer product,
    including the empty-list identity and negative factors. -/
theorem checkedProductFrom_sound
    (acc : ℤ) (xs : List ℤ) (value : ℤ)
    (h : checkedProductFrom acc xs = some value) :
    value = acc * xs.prod := by
  induction xs generalizing acc with
  | nil =>
      simp only [checkedProductFrom] at h
      cases Option.some.inj h
      simp
  | cons x xs ih =>
      cases hm : checkedMul acc x with
      | none =>
          simp [checkedProductFrom, hm] at h
      | some next =>
          have htail : checkedProductFrom next xs = some value := by
            simpa [checkedProductFrom, hm] using h
          calc
            value = next * xs.prod := ih next htail
            _ = acc * (x :: xs).prod := by
              rw [checkedMul_some hm]
              simp only [List.prod_cons]
              ring

/-- One component computes the products of its 0-weights and 1-weights,
    adds them, and refuses any out-of-range intermediate result. -/
def checkedComponent (block : List ℤ × List ℤ) : Option ℤ := do
  let atZero ← checkedProductFrom 1 block.1
  let atOne ← checkedProductFrom 1 block.2
  checkedAdd atZero atOne

theorem checkedComponent_sound
    (block : List ℤ × List ℤ) (value : ℤ)
    (h : checkedComponent block = some value) :
    value = block.1.prod + block.2.prod := by
  cases hzero : checkedProductFrom 1 block.1 with
  | none =>
      simp [checkedComponent, hzero] at h
  | some zero =>
      cases hone : checkedProductFrom 1 block.2 with
      | none =>
          simp [checkedComponent, hzero, hone] at h
      | some one =>
          cases hadd : checkedAdd zero one with
          | none =>
              simp [checkedComponent, hzero, hone, hadd] at h
          | some total =>
              have hv : value = zero + one := by
                have hvalue : total = value := by
                  simpa [checkedComponent, hzero, hone, hadd] using h
                exact hvalue.symm.trans (checkedAdd_some hadd)
              have hz := checkedProductFrom_sound 1 block.1 zero hzero
              have ho := checkedProductFrom_sound 1 block.2 one hone
              simpa [hz, ho] using hv

/-- Sequential multiplication of independently contracted component sums. -/
def checkedContractionFrom (acc : ℤ) :
    List (List ℤ × List ℤ) → Option ℤ
  | [] => some acc
  | block :: remaining =>
      (checkedComponent block).bind (fun factor =>
        (checkedMul acc factor).bind (fun next =>
          checkedContractionFrom next remaining))

theorem checkedContractionFrom_sound
    (acc : ℤ) (blocks : List (List ℤ × List ℤ)) (value : ℤ)
    (h : checkedContractionFrom acc blocks = some value) :
    value = acc * (blocks.map (fun block => block.1.prod + block.2.prod)).prod := by
  induction blocks generalizing acc with
  | nil =>
      simp only [checkedContractionFrom] at h
      cases Option.some.inj h
      simp
  | cons block rest ih =>
      cases hc : checkedComponent block with
      | none =>
          simp [checkedContractionFrom, hc] at h
      | some factor =>
          cases hm : checkedMul acc factor with
          | none =>
              simp [checkedContractionFrom, hc, hm] at h
          | some next =>
              have htail : checkedContractionFrom next rest = some value := by
                simpa [checkedContractionFrom, hc, hm] using h
              calc
                value =
                    next * (rest.map (fun b => b.1.prod + b.2.prod)).prod :=
                  ih next htail
                _ = acc * ((block :: rest).map
                    (fun b => b.1.prod + b.2.prod)).prod := by
                  rw [checkedMul_some hm, checkedComponent_sound block factor hc]
                  simp only [List.map_cons, List.prod_cons]
                  ring

/-- A successful full contraction always equals the exact mathematical
    product of two-term component sums. No favorable cancellations are
    allowed to conceal overflowing intermediate operations. -/
theorem checkedContraction_sound
    (blocks : List (List ℤ × List ℤ)) (value : ℤ)
    (h : checkedContractionFrom 1 blocks = some value) :
    value = (blocks.map (fun b => b.1.prod + b.2.prod)).prod := by
  simpa using checkedContractionFrom_sound 1 blocks value h

/-- The lower signed boundary is representable. -/
example : checkedMul (-(2 ^ 126 : ℤ)) 2 =
    some (-(2 ^ 127 : ℤ)) := by decide

/-- The upper positive 128-bit boundary is exclusive. -/
example : checkedAdd ((2 ^ 127 : ℤ) - 1) 1 = none := by decide

/-- An intermediate overflow is refused even when later multiplication by
    zero could make the final mathematical value small. -/
example : checkedProductFrom 1 [2 ^ 127, 0] = none := by decide

#print axioms ACC.CheckedComponentArithmetic.checkedMul_some
#print axioms ACC.CheckedComponentArithmetic.checkedProductFrom_sound
#print axioms ACC.CheckedComponentArithmetic.checkedComponent_sound
#print axioms ACC.CheckedComponentArithmetic.checkedContraction_sound

end ACC.CheckedComponentArithmetic
