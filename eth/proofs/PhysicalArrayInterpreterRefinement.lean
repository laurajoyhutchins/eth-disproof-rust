import OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-!
# Finite array-shaped state and source interpreter refinement

A Rust Config uses Option<usize>, fixed-length register arrays, and
VecDeque<bool> «stacks», while original BitProgram.Cfg uses Option (Fin l),
functions Fin r → Bool, and Fin s → List Bool. This file states an explicit
representation relation with refusal outside admitted widths and labels.

The concrete-shaped Lean executor below uses array reads, setIfInBounds and
head/tail list operations. It does NOT substitute the source execInstr in its
implementation. The general theorem, if discharged, is a Lean model theorem,
not a theorem about compiled Rust's actual memory or VecDeque library.
-/

namespace OAI.Algorithms.SubexponentialSAT.LeanRustRefinement

open BitProgram

/-- The information carried by Rust Config, with deque heads represented by
the first list cell and indices represented by natural numbers. -/
structure ArrayCfg where
  pc : Option Nat
  regs : Array Bool
  «stacks» : Array (List Bool)
deriving Repr, Inhabited

/-- The representation relation includes full array widths and all slots.
A dangling numeric PC is not a valid source state. -/
def Represents {r s l : ℕ} (raw : ArrayCfg) (cfg : Cfg r s l) : Prop :=
  raw.pc = cfg.pc.map Fin.val ∧
  raw.regs.size = r ∧
  (∀ i : Fin r, raw.regs[i.val]? = some (cfg.regs i)) ∧
  raw.«stacks».size = s ∧
  (∀ j : Fin s, raw.«stacks»[j.val]? = some (cfg.«stacks» j))

private def readReg {r : ℕ} (raw : ArrayCfg) (index : Fin r) : Bool :=
  (raw.regs[index.val]?).getD false

private def readStack {s : ℕ} (raw : ArrayCfg) (index : Fin s) : List Bool :=
  (raw.«stacks»[index.val]?).getD []

private def setReg {r : ℕ} (raw : ArrayCfg) (index : Fin r) (value : Bool) : ArrayCfg :=
  { raw with regs := raw.regs.setIfInBounds index.val value }

private def setStack {s : ℕ} (raw : ArrayCfg)
    (index : Fin s) (value : List Bool) : ArrayCfg :=
  { raw with «stacks» := raw.«stacks».setIfInBounds index.val value }

private def withPC {l : ℕ} (raw : ArrayCfg) (pc : Option (Fin l)) : ArrayCfg :=
  { raw with pc := pc.map Fin.val }

private def sourceWithPC {r s l : ℕ} (cfg : Cfg r s l)
    (pc : Option (Fin l)) : Cfg r s l :=
  { cfg with pc := pc }

private def sourceSetReg {r s l : ℕ} (cfg : Cfg r s l)
    (index : Fin r) (value : Bool) : Cfg r s l :=
  { cfg with regs := Function.update cfg.regs index value }

private def sourceSetStack {r s l : ℕ} (cfg : Cfg r s l)
    (index : Fin s) (value : List Bool) : Cfg r s l :=
  { cfg with «stacks» := Function.update cfg.«stacks» index value }

theorem represents_readReg {r s l : ℕ} {raw : ArrayCfg} {cfg : Cfg r s l}
    (h : Represents raw cfg) (index : Fin r) :
    readReg raw index = cfg.regs index := by
  rcases h with ⟨_, _, hregs, _, _⟩
  simp [readReg, hregs index]

theorem represents_readStack {r s l : ℕ} {raw : ArrayCfg} {cfg : Cfg r s l}
    (h : Represents raw cfg) (index : Fin s) :
    readStack raw index = cfg.«stacks» index := by
  rcases h with ⟨_, _, _, _, hstacks⟩
  simp [readStack, hstacks index]

theorem represents_withPC {r s l : ℕ} {raw : ArrayCfg} {cfg : Cfg r s l}
    (h : Represents raw cfg) (pc : Option (Fin l)) :
    Represents (withPC raw pc) (sourceWithPC cfg pc) := by
  rcases h with ⟨_, hregSize, hregs, hstackSize, hstacks⟩
  exact ⟨rfl, hregSize, hregs, hstackSize, hstacks⟩

theorem represents_setReg {r s l : ℕ} {raw : ArrayCfg} {cfg : Cfg r s l}
    (h : Represents raw cfg) (index : Fin r) (value : Bool) :
    Represents (setReg raw index value) (sourceSetReg cfg index value) := by
  rcases h with ⟨hpc, hregSize, hregs, hstackSize, hstacks⟩
  refine ⟨hpc, ?_, ?_, hstackSize, hstacks⟩
  · simpa [setReg] using hregSize
  · intro i
    have hin : index.val < raw.regs.size := by
      rw [hregSize]
      exact index.isLt
    by_cases hi : index = i
    · subst i
      simpa [setReg, sourceSetReg] using
        (Array.getElem?_setIfInBounds_self_of_lt
          (xs := raw.regs) (i := index.val) (a := value) hin)
    · have hne : index.val ≠ i.val := by
        intro he
        exact hi (Fin.ext he)
      rw [show (setReg raw index value).regs[i.val]? =
          raw.regs[i.val]? by
            simpa [setReg] using
              (Array.getElem?_setIfInBounds_ne (xs := raw.regs)
                (i := index.val) (j := i.val) (a := value) hne)]
      simpa [sourceSetReg, hi, Ne.symm hi] using hregs i

theorem represents_setStack {r s l : ℕ} {raw : ArrayCfg} {cfg : Cfg r s l}
    (h : Represents raw cfg) (index : Fin s) (value : List Bool) :
    Represents (setStack raw index value) (sourceSetStack cfg index value) := by
  rcases h with ⟨hpc, hregSize, hregs, hstackSize, hstacks⟩
  refine ⟨hpc, hregSize, hregs, ?_, ?_⟩
  · simpa [setStack] using hstackSize
  · intro j
    have hin : index.val < raw.«stacks».size := by
      rw [hstackSize]
      exact index.isLt
    by_cases hj : index = j
    · subst j
      simpa [setStack, sourceSetStack] using
        (Array.getElem?_setIfInBounds_self_of_lt
          (xs := raw.«stacks») (i := index.val) (a := value) hin)
    · have hne : index.val ≠ j.val := by
        intro he
        exact hj (Fin.ext he)
      rw [show (setStack raw index value).«stacks»[j.val]? =
          raw.«stacks»[j.val]? by
            simpa [setStack] using
              (Array.getElem?_setIfInBounds_ne (xs := raw.«stacks»)
                (i := index.val) (j := j.val) (a := value) hne)]
      simpa [sourceSetStack, hj, Ne.symm hj] using hstacks j

/-- Numeric PC admission is exact: a halted state is distinct from an
out-of-range active label. -/
def decodePC (l : ℕ) : Option Nat → Option (Option (Fin l))
  | none => some none
  | some n => if h : n < l then some (some ⟨n, h⟩) else none

theorem decodePC_in_range {l n : ℕ} (h : n < l) :
    decodePC l (some n) = some (some ⟨n, h⟩) := by
  simp [decodePC, h]

theorem decodePC_refuses_invalid {l n : ℕ} (h : ¬ n < l) :
    decodePC l (some n) = none := by
  simp [decodePC, h]

theorem represents_pc_admitted {r s l : ℕ} {raw : ArrayCfg}
    {cfg : Cfg r s l} (h : Represents raw cfg) :
    decodePC l raw.pc = some cfg.pc := by
  rcases h with ⟨hpc, _, _, _, _⟩
  cases hc : cfg.pc with
  | none =>
      simp [hpc, hc, decodePC]
  | some pc =>
      simp [hpc, hc, decodePC, pc.isLt]

/-- Both Rust register writes happen in source order. In particular, when
value and present alias, the later presence write wins. -/
theorem represents_readRegs {r s l : ℕ} {raw : ArrayCfg} {cfg : Cfg r s l}
    (h : Represents raw cfg) (value present : Fin r) (top : Option Bool) :
    Represents
      (setReg (setReg raw value (top.getD false)) present top.isSome)
      { cfg with regs := BitProgram.readRegs cfg.regs value present top } := by
  simpa [sourceSetReg, BitProgram.readRegs] using
    (represents_setReg
      (represents_setReg h value (top.getD false)) present top.isSome)

/-- A concrete-shaped executor: direct optional array reads and in-bounds
array updates. It does not invoke the Lean source execInstr. Calls to this
function require admitted widths; refusal is imposed by arrayStep. -/
private def execArrayInstr {r s l : ℕ}
    (instr : Instr r s l) (raw : ArrayCfg) : ArrayCfg :=
  match instr with
  | .halt => withPC raw (none : Option (Fin l))
  | .goto next => withPC raw (some next)
  | .set dst value next =>
      withPC (setReg raw dst value) (some next)
  | .copy dst src next =>
      withPC (setReg raw dst (readReg raw src)) (some next)
  | .bnot dst src next =>
      withPC (setReg raw dst (!(readReg raw src))) (some next)
  | .band dst left right next =>
      withPC (setReg raw dst (readReg raw left && readReg raw right)) (some next)
  | .bor dst left right next =>
      withPC (setReg raw dst (readReg raw left || readReg raw right)) (some next)
  | .bxor dst left right next =>
      withPC (setReg raw dst (readReg raw left ^^ readReg raw right)) (some next)
  | .branch test yes no =>
      withPC raw (some (if readReg raw test then yes else no))
  | .push stack src next =>
      withPC
        (setStack raw stack (readReg raw src :: readStack raw stack))
        (some next)
  | .peek stack value present next =>
      let top := (readStack raw stack).head?
      withPC
        (setReg (setReg raw value (top.getD false)) present top.isSome)
        (some next)
  | .pop stack value present next =>
      let cells := readStack raw stack
      let top := cells.head?
      withPC
        (setReg
          (setReg (setStack raw stack cells.tail) value (top.getD false))
          present top.isSome)
        (some next)

/-- For *every* admitted array-shaped state and all twelve source
instruction constructors, the independent array operations refine the
original source interpreter's exact one-step state, including aliases. -/
theorem execArrayInstr_refines {r s l : ℕ} {raw : ArrayCfg}
    {cfg : Cfg r s l} (h : Represents raw cfg) (instr : Instr r s l) :
    Represents (execArrayInstr instr raw) (BitProgram.execInstr instr cfg) := by
  cases instr with
  | halt =>
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC] using
        (represents_withPC h (none : Option (Fin l)))
  | goto next =>
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC] using
        (represents_withPC h (some next))
  | set dst value next =>
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC, sourceSetReg] using
        (represents_withPC (represents_setReg h dst value) (some next))
  | copy dst src next =>
      have hv := represents_readReg h src
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC, sourceSetReg, hv] using
        (represents_withPC (represents_setReg h dst (cfg.regs src)) (some next))
  | bnot dst src next =>
      have hv := represents_readReg h src
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC, sourceSetReg, hv] using
        (represents_withPC (represents_setReg h dst (!(cfg.regs src))) (some next))
  | band dst left right next =>
      have hl := represents_readReg h left
      have hr := represents_readReg h right
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC, sourceSetReg, hl, hr] using
        (represents_withPC
          (represents_setReg h dst (cfg.regs left && cfg.regs right)) (some next))
  | bor dst left right next =>
      have hl := represents_readReg h left
      have hr := represents_readReg h right
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC, sourceSetReg, hl, hr] using
        (represents_withPC
          (represents_setReg h dst (cfg.regs left || cfg.regs right)) (some next))
  | bxor dst left right next =>
      have hl := represents_readReg h left
      have hr := represents_readReg h right
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC, sourceSetReg, hl, hr] using
        (represents_withPC
          (represents_setReg h dst (cfg.regs left ^^ cfg.regs right)) (some next))
  | branch test yes no =>
      have ht := represents_readReg h test
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC, ht] using
        (represents_withPC h (some (if cfg.regs test then yes else no)))
  | push stack src next =>
      have hr := represents_readReg h src
      have hs := represents_readStack h stack
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC, sourceSetStack, hr, hs] using
        (represents_withPC
          (represents_setStack h stack (cfg.regs src :: cfg.«stacks» stack))
          (some next))
  | peek stack value present next =>
      let top : Option Bool := (cfg.«stacks» stack).head?
      have ht : (readStack raw stack).head? = top := by
        simp [top, represents_readStack h stack]
      have href := represents_readRegs h value present top
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC, ht, top] using
        (represents_withPC href (some next))
  | pop stack value present next =>
      let cells : List Bool := cfg.«stacks» stack
      let top : Option Bool := cells.head?
      have hs := represents_readStack h stack
      have ht : (readStack raw stack).head? = top := by
        simp [top, cells, hs]
      have hstack := represents_setStack h stack cells.tail
      have hregs := represents_readRegs hstack value present top
      simpa [execArrayInstr, BitProgram.execInstr, sourceWithPC,
        sourceSetStack, cells, top, hs, ht] using
        (represents_withPC hregs (some next))

/-- Distinguish invalid width or PC from a genuinely halted source program.
Error is a refusal, not an execution state, matching Rust's Result boundary. -/
def arrayStep {r s l : ℕ} (program : Program r s l)
    (raw : ArrayCfg) : Except Unit (Option ArrayCfg) :=
  if _ : raw.regs.size = r ∧ raw.«stacks».size = s then
    match raw.pc with
    | none => .ok none
    | some n =>
        if hn : n < l then
          .ok (some (execArrayInstr (program.code ⟨n, hn⟩) raw))
        else
          .error ()
  else
    .error ()

/-- The two outcomes of an admitted source step are preserved by the
array executor: stopped (no active PC), or an exact successor relation. -/
theorem arrayStep_refines {r s l : ℕ} (program : Program r s l)
    (raw : ArrayCfg) (cfg : Cfg r s l)
    (h : Represents raw cfg) :
    match BitProgram.step program cfg with
    | none => arrayStep program raw = .ok none
    | some nextCfg =>
        ∃ nextRaw, arrayStep program raw = .ok (some nextRaw) ∧
          Represents nextRaw nextCfg := by
  rcases h with ⟨hpc, hregSize, hregs, hstackSize, hstacks⟩
  cases hc : cfg.pc with
  | none =>
      simp [BitProgram.step, hc, arrayStep, hregSize, hstackSize, hpc]
  | some pc =>
      have hraw : raw.pc = some pc.val := by
        simpa [hc] using hpc
      have hrep : Represents raw cfg :=
        ⟨hpc, hregSize, hregs, hstackSize, hstacks⟩
      have hsim := execArrayInstr_refines hrep (program.code pc)
      simp only [BitProgram.step, hc, Option.map_some]
      refine ⟨execArrayInstr (program.code pc) raw, ?_, hsim⟩
      simp [arrayStep, hregSize, hstackSize, hraw, pc.isLt]

/-- An illegal active numeric label is always refused, even if the arrays
are otherwise well formed. It is never silently converted to a halt. -/
theorem arrayStep_refuses_invalidPC {r s l : ℕ} (program : Program r s l)
    (raw : ArrayCfg) (n : Nat)
    (hsize : raw.regs.size = r ∧ raw.«stacks».size = s)
    (hbad : ¬ n < l) :
    arrayStep program {raw with pc := some n} = .error () := by
  simp [arrayStep, hsize, hbad]

/-!
## Conditional native-deque operation contract

The preceding universal theorem is about a Lean array/list executor, not the
Rust standard library. Here we isolate the **four obligations** needed to
replace each model stack with a native deque: `front` observes the list head;
`push_front` prepends; `pop_front` returns the old head and exposes the
remaining tail. All statements below are conditional on these laws.

No Rust standard-library semantics is postulated as an unconditional axiom.
For the actual `std::collections::VecDeque<bool>`, these laws come from the
Rust library's published API contract and require a separate
implementation-to-specification justification. They are not proved by Lean.
-/

universe u

/-- Explicit host obligations for a deque whose logical front is list index
zero. Separating observations from operations prevents the list semantics
from being redefined as whatever the host operation happens to do. -/
structure DequeContract (D : Type u) where
  observe : D → List Bool
  front : D → Option Bool
  pushFront : D → Bool → D
  popFront : D → Option Bool × D
  front_spec : ∀ d, front d = (observe d).head?
  push_spec : ∀ d bit, observe (pushFront d bit) = bit :: observe d
  pop_value_spec : ∀ d, (popFront d).1 = (observe d).head?
  pop_rest_spec : ∀ d, observe (popFront d).2 = (observe d).tail

/-- Primitive host actions without a second program interpreter. -/
inductive DequeAction where
  | push (bit : Bool)
  | peek
  | pop
deriving Repr, DecidableEq

private def hostDequeOne {D : Type u} (c : DequeContract D)
    (a : DequeAction) (d : D) : Option Bool × D :=
  match a with
  | .push bit => (none, c.pushFront d bit)
  | .peek => (c.front d, d)
  | .pop => c.popFront d

private def listDequeOne (a : DequeAction) (xs : List Bool) :
    Option Bool × List Bool :=
  match a with
  | .push bit => (none, bit :: xs)
  | .peek => (xs.head?, xs)
  | .pop => (xs.head?, xs.tail)

/-- One operation of any host deque satisfying the contract produces exactly
the list result and observation, including the empty-pop case. -/
theorem hostDequeOne_refines {D : Type u} (c : DequeContract D)
    (a : DequeAction) (d : D) :
    (hostDequeOne c a d).1 = (listDequeOne a (c.observe d)).1 ∧
    c.observe (hostDequeOne c a d).2 =
      (listDequeOne a (c.observe d)).2 := by
  cases a with
  | push bit => exact ⟨rfl, c.push_spec d bit⟩
  | peek => exact ⟨c.front_spec d, rfl⟩
  | pop => exact ⟨c.pop_value_spec d, c.pop_rest_spec d⟩

private def hostDequeTrace {D : Type u} (c : DequeContract D) :
    List DequeAction → D → List (Option Bool) × D
  | [], d => ([], d)
  | a :: tail, d =>
      let one := hostDequeOne c a d
      let rest := hostDequeTrace c tail one.2
      (one.1 :: rest.1, rest.2)

private def listDequeTrace :
    List DequeAction → List Bool → List (Option Bool) × List Bool
  | [], xs => ([], xs)
  | a :: tail, xs =>
      let one := listDequeOne a xs
      let rest := listDequeTrace tail one.2
      (one.1 :: rest.1, rest.2)

/-- Universal, **conditional** trace correspondence. No number of actions,
stack contents, initial layout, or Boolean word length is fixed. -/
theorem hostDequeTrace_refines {D : Type u} (c : DequeContract D)
    (actions : List DequeAction) (d : D) :
    (hostDequeTrace c actions d).1 =
      (listDequeTrace actions (c.observe d)).1 ∧
    c.observe (hostDequeTrace c actions d).2 =
      (listDequeTrace actions (c.observe d)).2 := by
  induction actions generalizing d with
  | nil =>
      exact ⟨rfl, rfl⟩
  | cons a tail ih =>
      obtain ⟨hvalue, hstate⟩ := hostDequeOne_refines c a d
      obtain ⟨hresults, hfinal⟩ := ih (hostDequeOne c a d).2
      constructor
      · change (hostDequeOne c a d).1 ::
            (hostDequeTrace c tail (hostDequeOne c a d).2).1 =
          (listDequeOne a (c.observe d)).1 ::
            (listDequeTrace tail (listDequeOne a (c.observe d)).2).1
        rw [hvalue, ← hstate]
        exact congrArg (List.cons (listDequeOne a (c.observe d)).1) hresults
      · change c.observe (hostDequeTrace c tail (hostDequeOne c a d).2).2 =
            (listDequeTrace tail (listDequeOne a (c.observe d)).2).2
        rw [← hstate]
        exact hfinal

/-- The host observation for Peek agrees with the already proved
array-shaped model whenever the host stack decodes to the source slot. -/
theorem deque_front_matches_model {D : Type u} (c : DequeContract D)
    (d : D) (xs : List Bool) (h : c.observe d = xs) :
    c.front d = xs.head? := by
  rw [c.front_spec d, h]

/-- A host Push satisfies the existing full-register-and-stack representation
relation, not just equality of the one modified source stack. -/
theorem deque_push_preserves_represents {D : Type u} (c : DequeContract D)
    {r s l : ℕ} {raw : ArrayCfg} {cfg : Cfg r s l}
    (h : Represents raw cfg) (port : Fin s) (host : D) (bit : Bool)
    (hport : c.observe host = cfg.«stacks» port) :
    Represents
      (setStack raw port (c.observe (c.pushFront host bit)))
      (sourceSetStack cfg port (bit :: cfg.«stacks» port)) := by
  rw [c.push_spec host bit, hport]
  exact represents_setStack h port (bit :: cfg.«stacks» port)

/-- A host Pop must preserve the whole representation **and** return the
original list head, even for an empty source stack. -/
theorem deque_pop_preserves_represents {D : Type u} (c : DequeContract D)
    {r s l : ℕ} {raw : ArrayCfg} {cfg : Cfg r s l}
    (h : Represents raw cfg) (port : Fin s) (host : D)
    (hport : c.observe host = cfg.«stacks» port) :
    Represents
      (setStack raw port (c.observe (c.popFront host).2))
      (sourceSetStack cfg port (cfg.«stacks» port).tail) ∧
    (c.popFront host).1 = (cfg.«stacks» port).head? := by
  constructor
  · rw [c.pop_rest_spec host, hport]
    exact represents_setStack h port (cfg.«stacks» port).tail
  · rw [c.pop_value_spec host, hport]


/-!
## Exact source live-stack accounting, including resource refusal

The Rust bit-program interpreter maintains a running count of live deque cells
rather than scanning all stacks on every instruction. A pushed bit increases
that count by one; a nonempty pop decreases it by one; an empty pop does
nothing. All other instructions conserve it.

These are *universal Lean source-machine facts*. The Rust implementation and
the source graph's serialized representation remain independent proof
boundaries. Importantly, the cap test below justifies the local Rust
`live_bits >= max_stack_bits` preflight on pushes, not any claim about OS
memory or CPU complexity.
-/

open scoped BigOperators

/-- Total live source stack cells, counting the top of each stack as one bit. -/
def sourceLiveStackBits {r s l : ℕ} (cfg : Cfg r s l) : ℕ :=
  ∑ port : Fin s, (cfg.«stacks» port).length

/-- Per-stack gain: only the target of a physical Push receives one bit. -/
private def localPushGain {r s l : ℕ}
    (instr : Instr r s l) (port : Fin s) : ℕ :=
  match instr with
  | .push changed _ _ => if port = changed then 1 else 0
  | _ => 0

/-- Per-stack loss: only a nonempty physical Pop removes one bit. -/
private def localPopLoss {r s l : ℕ}
    (instr : Instr r s l) (cfg : Cfg r s l) (port : Fin s) : ℕ :=
  match instr with
  | .pop changed _ _ _ =>
      if port = changed ∧ (cfg.«stacks» changed).head? ≠ none then 1 else 0
  | _ => 0

/-- The scalar push increment used in the actual Rust live-bit preflight. -/
def sourcePushGain {r s l : ℕ} (instr : Instr r s l) : ℕ :=
  match instr with
  | .push _ _ _ => 1
  | _ => 0

/-- The scalar pop decrement used in the actual Rust live-bit preflight. -/
def sourcePopLoss {r s l : ℕ}
    (instr : Instr r s l) (cfg : Cfg r s l) : ℕ :=
  match instr with
  | .pop changed _ _ _ =>
      if (cfg.«stacks» changed).head? ≠ none then 1 else 0
  | _ => 0

/-- At *every* stack, for all twelve instructions, the change in length
is exactly the local push gain minus the local nonempty-pop loss. -/
theorem sourceStackLength_balance {r s l : ℕ}
    (instr : Instr r s l) (cfg : Cfg r s l) (port : Fin s) :
    ((BitProgram.execInstr instr cfg).«stacks» port).length +
      localPopLoss instr cfg port =
    (cfg.«stacks» port).length + localPushGain instr port := by
  cases instr with
  | halt => rfl
  | goto next => rfl
  | set dst value next => rfl
  | copy dst src next => rfl
  | bnot dst src next => rfl
  | band dst a b next => rfl
  | bor dst a b next => rfl
  | bxor dst a b next => rfl
  | branch test yes no => rfl
  | push stack src next =>
      by_cases h : port = stack
      · subst port
        simp [localPushGain, localPopLoss, BitProgram.execInstr]
      · simp [localPushGain, localPopLoss, BitProgram.execInstr, h]
  | peek stack value present next => rfl
  | pop stack value present next =>
      by_cases h : port = stack
      · subst port
        cases hs : cfg.«stacks» stack with
        | nil =>
            simp [localPushGain, localPopLoss, BitProgram.execInstr, hs]
        | cons bit tail =>
            simp [localPushGain, localPopLoss, BitProgram.execInstr, hs]
      · simp [localPushGain, localPopLoss, BitProgram.execInstr, h]

private theorem sourcePushGain_sum {r s l : ℕ} (instr : Instr r s l) :
    (∑ port : Fin s, localPushGain instr port) = sourcePushGain instr := by
  cases instr <;> simp [localPushGain, sourcePushGain]

private theorem sourcePopLoss_sum {r s l : ℕ}
    (instr : Instr r s l) (cfg : Cfg r s l) :
    (∑ port : Fin s, localPopLoss instr cfg port) = sourcePopLoss instr cfg := by
  cases instr with
  | pop stack value present next =>
      cases hs : cfg.«stacks» stack with
      | nil => simp [localPopLoss, sourcePopLoss, hs]
      | cons bit tail => simp [localPopLoss, sourcePopLoss, hs]
  | halt => simp [localPopLoss, sourcePopLoss]
  | goto next => simp [localPopLoss, sourcePopLoss]
  | set dst value next => simp [localPopLoss, sourcePopLoss]
  | copy dst src next => simp [localPopLoss, sourcePopLoss]
  | bnot dst src next => simp [localPopLoss, sourcePopLoss]
  | band dst a b next => simp [localPopLoss, sourcePopLoss]
  | bor dst a b next => simp [localPopLoss, sourcePopLoss]
  | bxor dst a b next => simp [localPopLoss, sourcePopLoss]
  | branch test yes no => simp [localPopLoss, sourcePopLoss]
  | push stack src next => simp [localPopLoss, sourcePopLoss]
  | peek stack value present next => simp [localPopLoss, sourcePopLoss]

/-- Universal exact live-stack accounting for a physical source instruction.
This covers empty pops and arbitrary register aliases without a state sample. -/
theorem sourceLiveStackBits_step {r s l : ℕ}
    (instr : Instr r s l) (cfg : Cfg r s l) :
    sourceLiveStackBits (BitProgram.execInstr instr cfg) +
      sourcePopLoss instr cfg =
    sourceLiveStackBits cfg + sourcePushGain instr := by
  have hsum :
      (Finset.univ.sum (fun port : Fin s =>
        ((BitProgram.execInstr instr cfg).«stacks» port).length +
          localPopLoss instr cfg port)) =
      (Finset.univ.sum (fun port : Fin s =>
        (cfg.«stacks» port).length + localPushGain instr port)) := by
    apply Finset.sum_congr rfl
    intro port _
    exact sourceStackLength_balance instr cfg port
  simpa only [Finset.sum_add_distrib, sourceLiveStackBits,
    sourcePushGain_sum, sourcePopLoss_sum] using hsum

/-- The exact Rust push preflight is sufficient for source live-bit capacity:
non-push operations never increase the number of live bits, and a push is
accepted only with a strictly available cell. No fixed stack or width bound. -/
theorem sourceLiveStackBits_step_capacity {r s l : ℕ}
    (instr : Instr r s l) (cfg : Cfg r s l) (maxBits : ℕ)
    (hcurrent : sourceLiveStackBits cfg ≤ maxBits)
    (hpush : sourcePushGain instr = 1 →
      sourceLiveStackBits cfg < maxBits) :
    sourceLiveStackBits (BitProgram.execInstr instr cfg) ≤ maxBits := by
  have hbalance := sourceLiveStackBits_step instr cfg
  have hgain : sourcePushGain instr ≤ 1 := by
    cases instr <;> simp [sourcePushGain]
  by_cases hp : sourcePushGain instr = 1
  · have havail := hpush hp
    omega
  · omega


/-!
## Exact admission and refusal at a bounded source instruction

The original \`execInstr\` is unbounded. This *partial* operation adds the
push-only capacity gate used by the Rust bounded runner without changing the
source instruction. \`none\` means capacity refusal, not source halting or a
valid final answer. This is a pure Lean model of the admission rule; the
host's cached usize counter and allocation behavior are still to be verified.
-/

/-- Preflight a single original source instruction. No state is produced on
refusal; accepted instructions use the original source transition exactly. -/
def sourceBoundedInstr {r s l : ℕ} (maxBits : ℕ)
    (instr : Instr r s l) (cfg : Cfg r s l) : Option (Cfg r s l) :=
  if sourcePushGain instr = 1 ∧ maxBits ≤ sourceLiveStackBits cfg then
    none
  else
    some (BitProgram.execInstr instr cfg)

/-- A bounded source instruction refuses *exactly* on a push at full
capacity, not on a non-push or an empty pop. -/
theorem sourceBoundedInstr_refuses_iff {r s l : ℕ}
    (maxBits : ℕ) (instr : Instr r s l) (cfg : Cfg r s l) :
    sourceBoundedInstr maxBits instr cfg = none ↔
      sourcePushGain instr = 1 ∧ maxBits ≤ sourceLiveStackBits cfg := by
  by_cases h : sourcePushGain instr = 1 ∧ maxBits ≤ sourceLiveStackBits cfg
  · simp [sourceBoundedInstr, h]
  · simp [sourceBoundedInstr, h]

/-- Admission has no alternative successor: the result is exactly the
original unbounded source instruction, and the refusal guard was false. -/
theorem sourceBoundedInstr_success {r s l : ℕ}
    (maxBits : ℕ) (instr : Instr r s l) (cfg next : Cfg r s l)
    (hstep : sourceBoundedInstr maxBits instr cfg = some next) :
    next = BitProgram.execInstr instr cfg ∧
      ¬ (sourcePushGain instr = 1 ∧
        maxBits ≤ sourceLiveStackBits cfg) := by
  by_cases h : sourcePushGain instr = 1 ∧ maxBits ≤ sourceLiveStackBits cfg
  · simp [sourceBoundedInstr, h] at hstep
  · have heq : BitProgram.execInstr instr cfg = next := by
      simpa [sourceBoundedInstr, h] using hstep
    exact ⟨heq.symm, h⟩

/-- Every successful bounded transition is within the configured logical
stack cap, including zero cap and aliased registers. The initial cap is
necessary: an already oversized state is rejected by Rust before stepping. -/
theorem sourceBoundedInstr_preserves_capacity {r s l : ℕ}
    (maxBits : ℕ) (instr : Instr r s l) (cfg next : Cfg r s l)
    (hcurrent : sourceLiveStackBits cfg ≤ maxBits)
    (hstep : sourceBoundedInstr maxBits instr cfg = some next) :
    sourceLiveStackBits next ≤ maxBits := by
  obtain ⟨rfl, hnot⟩ :=
    sourceBoundedInstr_success maxBits instr cfg next hstep
  apply sourceLiveStackBits_step_capacity instr cfg maxBits hcurrent
  intro hp
  have havail : ¬ maxBits ≤ sourceLiveStackBits cfg := by
    intro hfull
    exact hnot ⟨hp, hfull⟩
  omega

end OAI.Algorithms.SubexponentialSAT.LeanRustRefinement
