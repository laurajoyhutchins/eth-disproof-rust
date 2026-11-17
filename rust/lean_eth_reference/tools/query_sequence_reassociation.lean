import OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-!
# Reassociation of original finite StructuredCalls sequences

This theorem is about the original OpenAI Lean definition of Cmd and Eval.
It does not assume a Rust interpreter or a particular list of port indices.

A binary tree of source commands is interpreted in two ways:
1. by the original Cmd.seq constructors;
2. by its ordered list of leaves, with a cost-indexed state relation.

Every binary association of the *same ordered leaves* has precisely the
same Eval relation, including the number of source instruction steps.

The result does not certify the external Python source parser, the particular
Rust JSON receipt, or compiler object/ownership semantics.
-/

namespace OAI.Algorithms.SubexponentialSAT.PrepareReassociation

open StructuredCalls

private abbrev C := StructuredCalls.Cmd
private abbrev St := StructuredCalls.State

private abbrev CostRel (r s : ℕ) := ℕ → St r s → St r s → Prop

private def denotes {r s : ℕ} (c : C r s) : CostRel r s :=
  fun n a b => StructuredCalls.Eval c n a b

private def relId {r s : ℕ} : CostRel r s :=
  fun n a b => n = 0 ∧ a = b

private def relSeq {r s : ℕ} (x y : CostRel r s) : CostRel r s :=
  fun n a c => ∃ p q b, n = p + q ∧ x p a b ∧ y q b c

private theorem relSeq_assoc {r s : ℕ} (x y z : CostRel r s) :
    relSeq (relSeq x y) z = relSeq x (relSeq y z) := by
  funext n a c
  apply propext
  constructor
  · rintro ⟨pq, t, b, hn, ⟨p, q, mid, hpq, hx, hy⟩, hz⟩
    refine ⟨p, q + t, mid, ?_, hx, ⟨q, t, b, rfl, hy, hz⟩⟩
    simpa [hpq, Nat.add_assoc] using hn
  · rintro ⟨p, qt, mid, hn, hx, ⟨q, t, b, hqt, hy, hz⟩⟩
    refine ⟨p + q, t, b, ?_, ⟨p, q, mid, rfl, hx, hy⟩, hz⟩
    simpa [hqt, Nat.add_assoc] using hn

private theorem relSeq_id_left {r s : ℕ} (x : CostRel r s) :
    relSeq relId x = x := by
  funext n a b
  apply propext
  constructor
  · rintro ⟨p, q, mid, hn, ⟨hp, ha⟩, hx⟩
    subst p
    subst mid
    have hn' : n = q := by simpa using hn
    subst n
    exact hx
  · intro hx
    exact ⟨0, n, a, by simp, ⟨rfl, rfl⟩, hx⟩

private theorem relSeq_id_right {r s : ℕ} (x : CostRel r s) :
    relSeq x relId = x := by
  funext n a b
  apply propext
  constructor
  · rintro ⟨p, q, mid, hn, hx, ⟨hq, hb⟩⟩
    subst q
    subst b
    have hn' : n = p := by simpa using hn
    subst n
    exact hx
  · intro hx
    exact ⟨n, 0, b, by simp, hx, ⟨rfl, rfl⟩⟩

private theorem denotes_seq {r s : ℕ} (x y : C r s) :
    denotes (.seq x y) = relSeq (denotes x) (denotes y) := by
  funext n a c
  apply propext
  constructor
  · intro h
    cases h with
    | seq hx hy =>
      exact ⟨_, _, _, rfl, hx, hy⟩
  · rintro ⟨p, q, mid, hn, hx, hy⟩
    subst n
    exact StructuredCalls.Eval.seq hx hy

/-- A pure association tree; leaves retain their original commands. -/
inductive SeqTree (r s : ℕ) where
  | leaf (cmd : C r s)
  | node (left right : SeqTree r s)

/-- Interpret a tree by the original StructuredCalls.Cmd.seq. -/
def SeqTree.command {r s : ℕ} : SeqTree r s → C r s
  | .leaf c => c
  | .node left right => .seq left.command right.command

/-- Preserve the original left-to-right leaf order. -/
def SeqTree.leaves {r s : ℕ} : SeqTree r s → List (C r s)
  | .leaf c => [c]
  | .node left right => left.leaves ++ right.leaves

private def listDenotes {r s : ℕ} : List (C r s) → CostRel r s
  | [] => relId
  | c :: rest => relSeq (denotes c) (listDenotes rest)

private theorem listDenotes_append {r s : ℕ} (a b : List (C r s)) :
    listDenotes (a ++ b) = relSeq (listDenotes a) (listDenotes b) := by
  induction a with
  | nil =>
      simpa only [List.nil_append, listDenotes] using
        (relSeq_id_left (listDenotes b)).symm
  | cons c cs ih =>
      simp only [List.cons_append, listDenotes, ih]
      exact (relSeq_assoc (denotes c) (listDenotes cs) (listDenotes b)).symm

/-- Every ordered association tree denotes exactly its ordered leaf path.

In particular, left-recursive source syntax and adjacent balanced Rust
grouping preserve original Cmd.Eval for every state and instruction count.
-/
theorem tree_denotes_order {r s : ℕ} (t : SeqTree r s) :
    denotes t.command = listDenotes t.leaves := by
  induction t with
  | leaf c =>
      simpa only [SeqTree.command, SeqTree.leaves, listDenotes] using
        (relSeq_id_right (denotes c)).symm
  | node left right ihl ihr =>
      calc
        denotes (SeqTree.node left right).command =
            relSeq (denotes left.command) (denotes right.command) := by
              exact denotes_seq _ _
        _ = relSeq (listDenotes left.leaves) (listDenotes right.leaves) := by
              rw [ihl, ihr]
        _ = listDenotes (left.leaves ++ right.leaves) := by
              exact (listDenotes_append _ _).symm
        _ = listDenotes (SeqTree.node left right).leaves := rfl

/-- Any two sequence trees with the same ordered leaves have identical
cost-indexed state transitions in the original Lean semantics. -/
theorem tree_reassociation {r s : ℕ} (a b : SeqTree r s)
    (same_order : a.leaves = b.leaves)
    (n : ℕ) (start finish : St r s) :
    StructuredCalls.Eval a.command n start finish ↔
      StructuredCalls.Eval b.command n start finish := by
  have h := (tree_denotes_order a).trans
    ((congrArg listDenotes same_order).trans (tree_denotes_order b).symm)
  change denotes a.command n start finish ↔ denotes b.command n start finish
  rw [h]

end OAI.Algorithms.SubexponentialSAT.PrepareReassociation
