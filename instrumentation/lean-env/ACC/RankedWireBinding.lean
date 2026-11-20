import Mathlib
import ACC.CompleteExecutionTrace

/-!
# Input-byte-bound complete execution certificates

The earlier checker takes typed Fin indices. A malicious emitter could claim
a different graph and weight array from the actual caller-supplied input.
This module therefore takes the raw bytes as an *independent input* and
checks that the complete typed certificate encodes byte-for-byte to those
bytes under a fixed, versioned wire format. No unknown bytes or extra suffix
are silently ignored, and no SHA digest is substituted for a full equality.

A successful check is a theorem about the supplied raw bytes and claim for
*any finite input size*. This is not a theorem that compiled Rust uses the
same encoder/decoder. That source-language boundary needs verified Rust
extraction or an equivalent compiler refinement.
-/

namespace ACC.RankedWireBinding

open ACC.CompleteExecutionTrace
open ACC.ArithmeticReceipts
open ACC.CheckedI128BitVec

/-- Canonical little-endian byte sequence, with fixed field width.
    Arithmetic is on Nat rather than truncated machine numerals. -/
def littleBytes (width value : ℕ) : List UInt8 :=
  (List.range width).map fun i => UInt8.ofNat ((value / (256 ^ i)) % 256)

def u64Bytes (value : ℕ) : List UInt8 := littleBytes 8 value
def wordBytes (value : Word) : List UInt8 := littleBytes 16 value.toNat

/-- Exact version-1 representation, matching the Rust ranked-input module:
    RKC1, counts, source edges, labels, roots, source-index parents, ranks,
    and signed words. A missing parent is the 64-bit all-ones sentinel. -/
def encodeRankedWire {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (parent : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ)
    (weight : Fin n → Bool → Word) : List UInt8 :=
  let header : List UInt8 := [82, 75, 67, 49]
  let counts := u64Bytes n ++ u64Bytes c ++ u64Bytes edges.length
  let edgeFields := edges.flatMap fun edge =>
    u64Bytes edge.1.val ++ u64Bytes edge.2.val
  let labelFields := (List.finRange n).flatMap fun i => u64Bytes (label i).val
  let rootFields := (List.finRange c).flatMap fun k => u64Bytes (root k).val
  let parentFields := (List.finRange n).flatMap fun i =>
    u64Bytes (match parent i with
      | none => 2 ^ 64 - 1
      | some index => index.val)
  let rankFields := (List.finRange n).flatMap fun i => u64Bytes (rank i)
  let weights := (List.finRange n).flatMap fun i =>
    wordBytes (weight i false) ++ wordBytes (weight i true)
  header ++ counts ++ edgeFields ++ labelFields ++
    rootFields ++ parentFields ++ rankFields ++ weights

/-- The Rust v1 decoder only represents these finite machine indices.
    The sentinel is reserved for absence and cannot be a present parent.
    The guard's class count may be zero when n = 0. -/
def FitsWire {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (rank : Fin n → ℕ) : Prop :=
  c ≤ n ∧ n < 2 ^ 64 ∧ c < 2 ^ 64 ∧
    edges.length < 2 ^ 64 ∧ ∀ i : Fin n, rank i < 2 ^ 64

/-- Claims and observed arithmetic are untrusted. The verifier compares
    every caller-supplied input byte against an independent canonical
    encoding, as well as the complete signed-word execution and indexed
    source-edge certificate. No second integer-array execution is needed. -/
def checkWireClaim {n c : ℕ}
    (rawBytes : List UInt8)
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (parent : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ)
    (weight : Fin n → Bool → Word)
    (trace : List Receipt) (reported : Option Word) : Bool :=
  decide (FitsWire (c := c) edges rank) &&
  decide (encodeRankedWire edges label root parent rank weight = rawBytes) &&
  checkComplete edges label root parent rank weight trace reported

/-- Universal source-byte binding: every accepted claim is the exact,
    complete v1 encoding of the asserted finite source, not just a hash
    match or agreement on a prefix. -/
theorem checkWireClaim_bytes {n c : ℕ}
    (rawBytes : List UInt8)
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (parent : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ)
    (weight : Fin n → Bool → Word)
    (trace : List Receipt) (reported : Option Word)
    (h : checkWireClaim rawBytes edges label root parent rank
      weight trace reported = true) :
    encodeRankedWire edges label root parent rank weight = rawBytes := by
  simp only [checkWireClaim, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- Exact optional output correspondence follows for every accepted
    byte-bound report, including a checked overflow refusal. -/
theorem checkWireClaim_result {n c : ℕ}
    (rawBytes : List UInt8)
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (parent : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ)
    (weight : Fin n → Bool → Word)
    (trace : List Receipt) (reported : Option Word)
    (h : checkWireClaim rawBytes edges label root parent rank
      weight trace reported = true) :
    ACC.ArrayFinishSimulation.checkedArrayContraction
      (ACC.ComponentFoldCorrespondence.sourceItems label
        (fun i bit => (weight i bit).toInt)) =
        reported.map BitVec.toInt := by
  have hcomplete : checkComplete edges label root parent rank
      weight trace reported = true := by
    simp only [checkWireClaim, Bool.and_eq_true] at h
    exact h.2
  exact checkComplete_result edges label root parent rank
    weight trace reported hcomplete

/-- The successful output equals the literal source-edge-restricted sum,
    provided the supplied bytes and the entire trace are accepted.
    The mathematical statement is not conditional on finite test vectors. -/
theorem checkWireClaim_success_sound {n c : ℕ}
    (rawBytes : List UInt8)
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (parent : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ)
    (weight : Fin n → Bool → Word)
    (trace : List Receipt) (value : Word)
    (h : checkWireClaim rawBytes edges label root parent rank
      weight trace (some value) = true) :
    value.toInt =
      (∑ x : {x : Fin n → Bool // ∀ e ∈ edges, x e.1 = x e.2},
        ∏ i : Fin n, (weight i (x.1 i)).toInt) := by
  have hcomplete : checkComplete edges label root parent rank
      weight trace (some value) = true := by
    simp only [checkWireClaim, Bool.and_eq_true] at h
    exact h.2
  exact checkComplete_success_sound edges label root parent rank
    weight trace value hcomplete

/-- A zero-vertex source has a unique 28-byte header (no data rows). -/
example :
    (encodeRankedWire (n := 0) (c := 0)
      ([] : List (Fin 0 × Fin 0))
      (fun i => i.elim0) (fun k => k.elim0)
      (fun i => i.elim0) (fun i => i.elim0)
      (fun i _ => i.elim0)).length = 28 := by decide

#print axioms ACC.RankedWireBinding.checkWireClaim_bytes
#print axioms ACC.RankedWireBinding.checkWireClaim_result
#print axioms ACC.RankedWireBinding.checkWireClaim_success_sound

end ACC.RankedWireBinding
