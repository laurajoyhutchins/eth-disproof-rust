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

end OAI.Algorithms.SubexponentialSAT.LeanRustRefinement
