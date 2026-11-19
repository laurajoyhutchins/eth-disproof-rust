import Mathlib

/-!
# A formal bit-level model of the Rust packed affine row transcript

The native producer stores each coefficient row as Vec<u64> and the
right-hand-side separately as Bool. We model one u64 as BitVec 64,
decode each of its bits, and prove that packed XOR/swap replay has
the same decoded effect as direct Boolean row replay.

This is a semantics theorem for the specified packed operations.
It is NOT an FFI proof that the native Rust code refines them.
-/

namespace IndependentETH.AffinePackedRows

abbrev Words (m w : ℕ) := Fin m → Fin w → BitVec 64
abbrev Bits (m w : ℕ) := Fin m → Fin w → Fin 64 → Bool

def decode {m w : ℕ} (rows : Words m w) : Bits m w :=
  fun row word bit => (rows row word).getLsbD bit.val

def packedSwap {m w : ℕ} (first second : Fin m) (rows : Words m w) :
    Words m w :=
  fun row word =>
    if row = first then rows second word
    else if row = second then rows first word
    else rows row word

def booleanSwap {m w : ℕ} (first second : Fin m) (rows : Bits m w) :
    Bits m w :=
  fun row word bit =>
    if row = first then rows second word bit
    else if row = second then rows first word bit
    else rows row word bit

def packedXor {m w : ℕ} (target source : Fin m) (rows : Words m w) :
    Words m w :=
  fun row word =>
    if row = target then rows target word ^^^ rows source word
    else rows row word

def booleanXor {m w : ℕ} (target source : Fin m) (rows : Bits m w) :
    Bits m w :=
  fun row word bit =>
    if row = target then rows target word bit ^^ rows source word bit
    else rows row word bit

theorem decode_swap {m w : ℕ} (first second : Fin m)
    (rows : Words m w) :
    decode (packedSwap first second rows) =
      booleanSwap first second (decode rows) := by
  funext row word bit
  by_cases h₁ : row = first <;> by_cases h₂ : row = second
  all_goals
    by_cases hs : second = first
    · simp_all [decode, packedSwap, booleanSwap]
    · simp_all [decode, packedSwap, booleanSwap]

theorem decode_xor {m w : ℕ} (target source : Fin m)
    (rows : Words m w) :
    decode (packedXor target source rows) =
      booleanXor target source (decode rows) := by
  funext row word bit
  by_cases h : row = target
  · subst row
    simp [decode, packedXor, booleanXor]
  · simp [decode, packedXor, booleanXor, h]

/-- The packed representation uses little-endian 64-bit words.
For a flattened column index, the source word is index / 64 and the
bit within that word is index % 64, even across 63/64/127/128. -/
def readColumn {m w : ℕ} (rows : Words m w)
    (row : Fin m) (column : Fin (w * 64)) : Bool :=
  (rows row ⟨column.val / 64, by have h := column.isLt; omega⟩).getLsbD
    (column.val % 64)

theorem readColumn_xor {m w : ℕ} (target source row : Fin m)
    (rows : Words m w) (column : Fin (w * 64)) :
    readColumn (packedXor target source rows) row column =
      if row = target then
        readColumn rows target column ^^ readColumn rows source column
      else readColumn rows row column := by
  by_cases h : row = target
  · subst row
    simp [readColumn, packedXor]
  · simp [readColumn, packedXor, h]

theorem word_and_bit_reconstruct {w : ℕ} (column : Fin (w * 64)) :
    column.val / 64 * 64 + column.val % 64 = column.val := by
  omega

inductive Step (m : ℕ) where
  | swap (first second : Fin m)
  | xor (target source : Fin m)

def applyPacked {m w : ℕ} (op : Step m) (rows : Words m w) :
    Words m w :=
  match op with
  | .swap first second => packedSwap first second rows
  | .xor target source => packedXor target source rows

def applyBoolean {m w : ℕ} (op : Step m) (rows : Bits m w) :
    Bits m w :=
  match op with
  | .swap first second => booleanSwap first second rows
  | .xor target source => booleanXor target source rows

theorem decode_apply {m w : ℕ} (op : Step m) (rows : Words m w) :
    decode (applyPacked op rows) = applyBoolean op (decode rows) := by
  cases op with
  | swap first second => exact decode_swap first second rows
  | xor target source => exact decode_xor target source rows

def replayPacked {m w : ℕ} : List (Step m) → Words m w → Words m w
  | [], rows => rows
  | op :: steps, rows => replayPacked steps (applyPacked op rows)

def replayBoolean {m w : ℕ} : List (Step m) → Bits m w → Bits m w
  | [], rows => rows
  | op :: steps, rows => replayBoolean steps (applyBoolean op rows)

theorem decode_replay {m w : ℕ} (steps : List (Step m))
    (rows : Words m w) :
    decode (replayPacked steps rows) =
      replayBoolean steps (decode rows) := by
  induction steps generalizing rows with
  | nil => rfl
  | cons op tail ih =>
      simp only [replayPacked, replayBoolean]
      rw [ih, decode_apply]

/-- The RHS is stored separately by the native Rust producer.
Its XOR operation is pure Bool.xor and does not depend on bit packing. -/
def rhsStep {m : ℕ} (op : Step m) (rhs : Fin m → Bool) : Fin m → Bool :=
  match op with
  | .swap first second =>
      fun row =>
        if row = first then rhs second
        else if row = second then rhs first
        else rhs row
  | .xor target source =>
      fun row => if row = target then rhs target ^^ rhs source else rhs row

def replayRhs {m : ℕ} : List (Step m) → (Fin m → Bool) → (Fin m → Bool)
  | [], rhs => rhs
  | op :: steps, rhs => replayRhs steps (rhsStep op rhs)

def replayAugmented {m w : ℕ}
    (steps : List (Step m))
    (rows : Words m w × (Fin m → Bool)) :
    Words m w × (Fin m → Bool) :=
  (replayPacked steps rows.1, replayRhs steps rows.2)

def decodeAugmented {m w : ℕ}
    (rows : Words m w × (Fin m → Bool)) :
    Bits m w × (Fin m → Bool) :=
  (decode rows.1, rows.2)

/-- For all finite row counts, 64-bit-word counts, transcripts and RHSs,
the full packed augmented matrix decodes to Boolean replay. -/
theorem decode_augmented_replay {m w : ℕ} (steps : List (Step m))
    (rows : Words m w × (Fin m → Bool)) :
    decodeAugmented (replayAugmented steps rows) =
      (replayBoolean steps (decode rows.1), replayRhs steps rows.2) := by
  simp [decodeAugmented, replayAugmented, decode_replay]


/-!
## Raw-value admission for the native certificate boundary

The Rust raw representation uses an 8-bit tag and 64-bit indices.
The following Lean model keeps the raw widths, rejects invalid tags,
aliases, out-of-bounds row numbers, invalid pivots and budget overruns,
and only then constructs well-typed finite row operations.

This formalizes the admission *specification*, not compiled Rust code.
-/

structure RawStep where
  tag : BitVec 8
  first : BitVec 64
  second : BitVec 64
  deriving DecidableEq, Repr

def validStep (m : ℕ) (raw : RawStep) : Prop :=
  (raw.tag.toNat = 0 ∨ raw.tag.toNat = 1) ∧
  raw.first.toNat < m ∧ raw.second.toNat < m ∧
  raw.first.toNat ≠ raw.second.toNat

def decodeStep (m : ℕ) (raw : RawStep) : Option (Step m) :=
  if h : validStep m raw then
    let first : Fin m := ⟨raw.first.toNat, h.2.1⟩
    let second : Fin m := ⟨raw.second.toNat, h.2.2.1⟩
    if raw.tag.toNat = 0 then
      some (.swap first second)
    else
      some (.xor first second)
  else none

theorem decodeStep_isSome_iff {m : ℕ} (raw : RawStep) :
    (decodeStep m raw).isSome = true ↔ validStep m raw := by
  by_cases h : validStep m raw
  · by_cases ht : raw.tag.toNat = 0
    · simp [decodeStep, h, ht]
    · simp [decodeStep, h, ht]
  · simp [decodeStep, h]

theorem decodeStep_rejects_unknown_tag {m : ℕ} (raw : RawStep)
    (h : raw.tag.toNat ≠ 0 ∧ raw.tag.toNat ≠ 1) :
    decodeStep m raw = none := by
  have bad : ¬validStep m raw := by
    intro hv
    rcases hv.1 with ht | ht
    · exact h.1 ht
    · exact h.2 ht
  simp [decodeStep, bad]

theorem decodeStep_rejects_out_of_bounds {m : ℕ} (raw : RawStep)
    (h : m ≤ raw.first.toNat ∨ m ≤ raw.second.toNat) :
    decodeStep m raw = none := by
  have bad : ¬validStep m raw := by
    intro hv
    rcases h with h | h
    · exact (Nat.not_lt_of_ge h) hv.2.1
    · exact (Nat.not_lt_of_ge h) hv.2.2.1
  simp [decodeStep, bad]

theorem decodeStep_rejects_aliased_rows {m : ℕ} (raw : RawStep)
    (h : raw.first.toNat = raw.second.toNat) :
    decodeStep m raw = none := by
  have bad : ¬validStep m raw := by
    intro hv
    exact hv.2.2.2 h
  simp [decodeStep, bad]

def decodeSteps (m : ℕ) : List RawStep → Option (List (Step m))
  | [] => some []
  | head :: tail => do
      let op ← decodeStep m head
      let rest ← decodeSteps m tail
      pure (op :: rest)

structure RawCertificate where
  version : BitVec 8
  steps : List RawStep
  pivotColumns : List (BitVec 64)

def validPivots (m k : ℕ) (pivots : List (BitVec 64)) : Prop :=
  pivots.length ≤ m ∧ pivots.length ≤ k ∧
  (pivots.map (fun col => col.toNat)).Pairwise (· < ·) ∧
  ∀ col ∈ pivots, col.toNat < k

def admissible (m k b maxCells maxSteps : ℕ)
    (cert : RawCertificate) : Prop :=
  cert.version.toNat = 1 ∧
  m * (k + b + 1) ≤ maxCells ∧
  cert.steps.length ≤ maxSteps ∧
  validPivots m k cert.pivotColumns

def decodeCertificate (m k b maxCells maxSteps : ℕ)
    (cert : RawCertificate) : Option (List (Step m)) :=
  if admissible m k b maxCells maxSteps cert then
    decodeSteps m cert.steps
  else none

theorem accepted_has_valid_version_and_budgets
    {m k b maxCells maxSteps : ℕ} {cert : RawCertificate}
    {ops : List (Step m)}
    (h : decodeCertificate m k b maxCells maxSteps cert = some ops) :
    admissible m k b maxCells maxSteps cert := by
  by_contra hn
  simp [decodeCertificate, hn] at h

theorem exceeded_budget_refuses
    {m k b maxCells maxSteps : ℕ} (cert : RawCertificate)
    (h : maxCells < m * (k + b + 1) ∨ maxSteps < cert.steps.length) :
    decodeCertificate m k b maxCells maxSteps cert = none := by
  have hn : ¬admissible m k b maxCells maxSteps cert := by
    intro ha
    rcases ha with ⟨_, cells, steps, _⟩
    rcases h with h | h <;> omega
  simp [decodeCertificate, hn]

def replayChecked {m w : ℕ} (k b maxCells maxSteps : ℕ)
    (cert : RawCertificate) (rows : Words m w) :
    Option (Words m w) := do
  let ops ← decodeCertificate m k b maxCells maxSteps cert
  pure (replayPacked ops rows)

/-- Every accepted raw transcript has a finite, well-typed witness and
decodes to the same Boolean row replay. Malformed inputs produce none. -/
theorem accepted_raw_replay_decodes
    {m w k b maxCells maxSteps : ℕ}
    (cert : RawCertificate) (rows terminal : Words m w)
    (h : replayChecked k b maxCells maxSteps cert rows = some terminal) :
    ∃ ops : List (Step m),
      decodeCertificate m k b maxCells maxSteps cert = some ops ∧
      decode terminal = replayBoolean ops (decode rows) := by
  unfold replayChecked at h
  cases hdec : decodeCertificate m k b maxCells maxSteps cert with
  | none => simp [hdec] at h
  | some ops =>
      simp [hdec] at h
      subst terminal
      exact ⟨ops, hdec, decode_replay ops rows⟩

example : decodeStep 2 ⟨0, 0, 1⟩ = some (.swap ⟨0, by omega⟩ ⟨1, by omega⟩) := by
  decide
example : decodeStep 2 ⟨1, 0, 1⟩ = some (.xor ⟨0, by omega⟩ ⟨1, by omega⟩) := by
  decide
example : decodeStep 2 ⟨255, 0, 1⟩ = none := by decide
example : decodeStep 2 ⟨0, 0, 0⟩ = none := by decide
example : decodeStep 2 ⟨1, 0, 18446744073709551615⟩ = none := by decide
example : decodeStep 0 ⟨0, 0, 1⟩ = none := by decide

#print axioms IndependentETH.AffinePackedRows.decodeStep_isSome_iff
#print axioms IndependentETH.AffinePackedRows.decodeStep_rejects_unknown_tag
#print axioms IndependentETH.AffinePackedRows.decodeStep_rejects_out_of_bounds
#print axioms IndependentETH.AffinePackedRows.decodeStep_rejects_aliased_rows
#print axioms IndependentETH.AffinePackedRows.accepted_has_valid_version_and_budgets
#print axioms IndependentETH.AffinePackedRows.exceeded_budget_refuses
#print axioms IndependentETH.AffinePackedRows.accepted_raw_replay_decodes

#print axioms IndependentETH.AffinePackedRows.decode_xor
#print axioms IndependentETH.AffinePackedRows.readColumn_xor
#print axioms IndependentETH.AffinePackedRows.word_and_bit_reconstruct
#print axioms IndependentETH.AffinePackedRows.decode_replay
#print axioms IndependentETH.AffinePackedRows.decode_augmented_replay
