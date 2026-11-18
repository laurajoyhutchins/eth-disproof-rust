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

#print axioms IndependentETH.AffinePackedRows.decode_xor
#print axioms IndependentETH.AffinePackedRows.readColumn_xor
#print axioms IndependentETH.AffinePackedRows.word_and_bit_reconstruct
#print axioms IndependentETH.AffinePackedRows.decode_replay
#print axioms IndependentETH.AffinePackedRows.decode_augmented_replay
