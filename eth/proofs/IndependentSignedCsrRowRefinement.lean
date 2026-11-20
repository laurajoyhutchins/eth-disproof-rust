/-!
# Signed-CSR single-row representation refinement

This file is a proof fragment appended after IndependentNonAffineRecurrence.lean
by the exact-head independent Lean workflow. Its definitions refer to the
actual executable decodeCsrRow, rather than a copy of that decoder.

The Rust-shaped *local* model checks columns before signs and encodes a
negative i8 literal as a true falsifying bit. In contrast, Lean's decoder
reads signs before checking sorted columns. Equality of their results proves
that reordering these pure checks does not change acceptance or refusal.

Scope: an in-bounds CSR row for which the three observed columns and signs
are explicit. This is not a compiler-level simulation of Rust slice access,
allocation, the whole CSR parser, or serialization.
-/

namespace IndependentETH.NonAffine

/-- Model the Rust sign test, checking positive polarity first.
The existing Lean specification checks negative polarity first. -/
def rustLiteralBit (z : Int) : Option Bool :=
  if z = 1 then some false
  else if z = -1 then some true
  else none

theorem rustLiteralBit_eq_polarityFromSign (z : Int) :
    rustLiteralBit z = polarityFromSign z := by
  by_cases hp : z = 1
  · have hn : z ≠ -1 := by omega
    simp [rustLiteralBit, polarityFromSign, hp, hn]
  · by_cases hn : z = -1
    · simp [rustLiteralBit, polarityFromSign, hp, hn]
    · simp [rustLiteralBit, polarityFromSign, hp, hn]

/-- A separate semantic model of one Rust-recognized three-literal slice.
It checks strict, in-range columns before decoding the three signed i8
polarity values, as the production Rust recognizer does. -/
def rustTripleRow (n a b c : Nat) (sa sb sc : Int) : Option SignedRow :=
  if a < b ∧ b < c ∧ c < n then do
    let pa ← rustLiteralBit sa
    let pb ← rustLiteralBit sb
    let pc ← rustLiteralBit sc
    pure (row a b c (pa, pb, pc))
  else none

/-- Rust's checked subtraction criterion and Lean's addition criterion
describe exactly the same row width when the offsets are ordered. -/
theorem rustWidth_iff_leanWidth (start stop : Nat) (h : start ≤ stop) :
    stop - start = 3 ↔ stop = start + 3 := by
  omega

/-- The complete one-row refinement. All source observations are stated
explicitly: two offsets, all three columns, and all three signs. The
subtraction-based slice check entails the equality required by the
existing Lean decoder. No sign or column can be silently dropped.

This proves BOTH acceptance and refusal equality for the witnessed row,
including bad signs, duplicate/out-of-range columns, and wrong column
order. Malformed offsets are treated by the separate refusal theorem.
-/
theorem rustTripleRow_eq_decodeCsrRow
    (csr : SignedCsrInput) (i start stop a b c : Nat)
    (sa sb sc : Int)
    (hstart : csr.offsets[i]? = some start)
    (hstop : csr.offsets[i + 1]? = some stop)
    (hshape : start ≤ stop ∧ stop ≤ csr.columns.length ∧ stop - start = 3)
    (ha : csr.columns[start]? = some a)
    (hb : csr.columns[start + 1]? = some b)
    (hc : csr.columns[start + 2]? = some c)
    (hsa : csr.signs[start]? = some sa)
    (hsb : csr.signs[start + 1]? = some sb)
    (hsc : csr.signs[start + 2]? = some sc) :
    rustTripleRow csr.variableCount a b c sa sb sc = decodeCsrRow csr i := by
  have hwidth : stop = start + 3 :=
    (rustWidth_iff_leanWidth start stop hshape.1).mp hshape.2.2
  cases hpa : polarityFromSign sa with
  | none =>
      simp [rustTripleRow, decodeCsrRow, rustLiteralBit_eq_polarityFromSign,
        hstart, hstop, hwidth, ha, hb, hc, hsa, hsb, hsc, hpa]
  | some pa =>
      cases hpb : polarityFromSign sb with
      | none =>
          simp [rustTripleRow, decodeCsrRow, rustLiteralBit_eq_polarityFromSign,
            hstart, hstop, hwidth, ha, hb, hc, hsa, hsb, hsc, hpa, hpb]
      | some pb =>
          cases hpc : polarityFromSign sc with
          | none =>
              simp [rustTripleRow, decodeCsrRow, rustLiteralBit_eq_polarityFromSign,
                hstart, hstop, hwidth, ha, hb, hc, hsa, hsb, hsc, hpa, hpb, hpc]
          | some pc =>
              simp [rustTripleRow, decodeCsrRow, rustLiteralBit_eq_polarityFromSign,
                hstart, hstop, hwidth, ha, hb, hc, hsa, hsb, hsc, hpa, hpb, hpc]

/-- Under the same witnessed, in-bounds row, all refusals agree, not only
successful outputs. A forbidden sign, unsorted or duplicated columns, or
an out-of-range column is rejected on both sides. -/
theorem rustTripleRow_refusal_iff
    (csr : SignedCsrInput) (i start stop a b c : Nat)
    (sa sb sc : Int)
    (hstart : csr.offsets[i]? = some start)
    (hstop : csr.offsets[i + 1]? = some stop)
    (hshape : start ≤ stop ∧ stop ≤ csr.columns.length ∧ stop - start = 3)
    (ha : csr.columns[start]? = some a)
    (hb : csr.columns[start + 1]? = some b)
    (hc : csr.columns[start + 2]? = some c)
    (hsa : csr.signs[start]? = some sa)
    (hsb : csr.signs[start + 1]? = some sb)
    (hsc : csr.signs[start + 2]? = some sc) :
    (rustTripleRow csr.variableCount a b c sa sb sc = none) ↔
      (decodeCsrRow csr i = none) := by
  rw [rustTripleRow_eq_decodeCsrRow csr i start stop a b c sa sb sc
    hstart hstop hshape ha hb hc hsa hsb hsc]

/-- A malformed local width is always refused by the original Lean decoder.
The preceding width theorem identifies the corresponding Rust subtraction
failure whenever the start and stop offsets are ordered. -/
theorem decodeCsrRow_badWidth
    (csr : SignedCsrInput) (i start stop : Nat)
    (hstart : csr.offsets[i]? = some start)
    (hstop : csr.offsets[i + 1]? = some stop)
    (hbad : stop ≠ start + 3) :
    decodeCsrRow csr i = none := by
  simp [decodeCsrRow, hstart, hstop, hbad]

/-- The supported machine boundary is explicit rather than silently
identifying arbitrarily large Lean natural numbers with Rust usize. -/
def rustRowMachineBounds (wordBits : Nat) (csr : SignedCsrInput)
    (start stop : Nat) (sa sb sc : Int) : Prop :=
  csr.variableCount < 2 ^ wordBits ∧
  csr.columns.length < 2 ^ wordBits ∧
  csr.signs.length = csr.columns.length ∧
  csr.offsets.length < 2 ^ wordBits ∧
  start < 2 ^ wordBits ∧ stop < 2 ^ wordBits ∧
  (-128 ≤ sa ∧ sa ≤ 127) ∧
  (-128 ≤ sb ∧ sb ≤ 127) ∧
  (-128 ≤ sc ∧ sc ≤ 127)

/-- Explicitly bounded specialization: if the Rust arrays can be represented
and the checked row witnesses are the ones read from those arrays, the
semantic decoders agree. The boundedness assumption here is about data
representation, not Rust execution or memory allocation. -/
theorem rustTripleRow_bounded_refinement
    (wordBits : Nat) (csr : SignedCsrInput) (i start stop a b c : Nat)
    (sa sb sc : Int)
    (_hMachine : rustRowMachineBounds wordBits csr start stop sa sb sc)
    (hstart : csr.offsets[i]? = some start)
    (hstop : csr.offsets[i + 1]? = some stop)
    (hshape : start ≤ stop ∧ stop ≤ csr.columns.length ∧ stop - start = 3)
    (ha : csr.columns[start]? = some a)
    (hb : csr.columns[start + 1]? = some b)
    (hc : csr.columns[start + 2]? = some c)
    (hsa : csr.signs[start]? = some sa)
    (hsb : csr.signs[start + 1]? = some sb)
    (hsc : csr.signs[start + 2]? = some sc) :
    rustTripleRow csr.variableCount a b c sa sb sc = decodeCsrRow csr i :=
  rustTripleRow_eq_decodeCsrRow csr i start stop a b c sa sb sc
    hstart hstop hshape ha hb hc hsa hsb hsc

#print axioms IndependentETH.NonAffine.rustLiteralBit_eq_polarityFromSign
#print axioms IndependentETH.NonAffine.rustWidth_iff_leanWidth
#print axioms IndependentETH.NonAffine.rustTripleRow_eq_decodeCsrRow
#print axioms IndependentETH.NonAffine.rustTripleRow_refusal_iff
#print axioms IndependentETH.NonAffine.decodeCsrRow_badWidth
#print axioms IndependentETH.NonAffine.rustTripleRow_bounded_refinement

end IndependentETH.NonAffine
