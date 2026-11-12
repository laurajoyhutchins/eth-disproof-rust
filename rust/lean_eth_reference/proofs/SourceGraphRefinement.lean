import OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-!
# Physical refinement for a generated compositional machine

The original Lean compiler already proves StructuredCalls.eval_trace. This file
supplies a compositional interface to *independently generated* physical code:
five constructor-specific obligations, a complete code-at-all-labels theorem,
and preservation of every one-step transition, trace and execution bound.

The agreement obligations are not assumed to be discharged by the Rust generator.
Source-bound differential acceptance remains a separate necessary gate.
-/

namespace OAI.Algorithms.SubexponentialSAT.LeanRustRefinement

open BitProgram

/-- An instruction agreement obligation at each static command site. -/
def SiteAgreement {r s l : ℕ} (c : StructuredCalls.Cmd r s)
    (p : Program r s l) (embed : StructuredCalls.Site c → Fin l)
    (exit : Fin l) : Prop :=
  ∀ site, p.code (embed site) = StructuredCalls.code c embed exit site

theorem site_base {r s l : ℕ} (c : StructuredProgram.Cmd r s)
    (p : Program r s l) (embed : StructuredProgram.Site c → Fin l)
    (exit : Fin l)
    (h : ∀ site, p.code (embed site) = StructuredProgram.code c embed exit site) :
    SiteAgreement (.base c) p embed exit :=
  h

/-- Include relocated halt-to-return, not just ordinary callee instructions. -/
theorem site_call {r s l m : ℕ} (callee : Program r s m)
    (p : Program r s l) (embed : Fin m → Fin l) (exit : Fin l)
    (h : ∀ site, p.code (embed site) =
      ProgramLinking.relocateInstr id id embed (some exit) (callee.code site)) :
    SiteAgreement (.call callee) p embed exit :=
  h

/-- The first block must branch to the entry of the second. -/
theorem site_seq {r s l : ℕ} (first second : StructuredCalls.Cmd r s)
    (p : Program r s l)
    (embed : StructuredCalls.Site (.seq first second) → Fin l)
    (exit : Fin l)
    (hf : SiteAgreement first p (fun q => embed (.inl q))
      (StructuredCalls.entry second (fun q => embed (.inr q)) exit))
    (hs : SiteAgreement second p (fun q => embed (.inr q)) exit) :
    SiteAgreement (.seq first second) p embed exit := by
  intro site
  cases site with
  | inl q => exact hf q
  | inr q => exact hs q

/-- The guard and both conditional branches are independent obligations. -/
theorem site_ite {r s l : ℕ} (test : Fin r)
    (yes no : StructuredCalls.Cmd r s) (p : Program r s l)
    (embed : StructuredCalls.Site (.ite test yes no) → Fin l)
    (exit : Fin l)
    (hguard : p.code (embed none) =
      Instr.branch test
        (StructuredCalls.entry yes (fun q => embed (some (.inl q))) exit)
        (StructuredCalls.entry no (fun q => embed (some (.inr q))) exit))
    (hy : SiteAgreement yes p (fun q => embed (some (.inl q))) exit)
    (hn : SiteAgreement no p (fun q => embed (some (.inr q))) exit) :
    SiteAgreement (.ite test yes no) p embed exit := by
  intro site
  cases site with
  | none => exact hguard
  | some q =>
      cases q with
      | inl x => exact hy x
      | inr x => exact hn x

/-- Loop back-edges return to the guard; a false guard exits the block. -/
theorem site_while {r s l : ℕ} (test : Fin r)
    (body : StructuredCalls.Cmd r s) (p : Program r s l)
    (embed : StructuredCalls.Site (.while test body) → Fin l)
    (exit : Fin l)
    (hguard : p.code (embed none) =
      Instr.branch test
        (StructuredCalls.entry body (fun q => embed (some q)) (embed none))
        exit)
    (hb : SiteAgreement body p (fun q => embed (some q)) (embed none)) :
    SiteAgreement (.while test body) p embed exit := by
  intro site
  cases site with
  | none => exact hguard
  | some x => exact hb x

/-- The graph emitter must discharge every field to obtain this certificate. -/
structure WholeAgreement {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (candidate : Program r s (StructuredCalls.size c + 1))
    (input output : Fin s) : Prop where
  input_port : candidate.inputStack = input
  output_port : candidate.outputStack = output
  source_entry : candidate.entry =
    StructuredCalls.entry c (StructuredCalls.siteAddress c)
      (StructuredCalls.exitAddress c)
  sites : SiteAgreement c candidate (StructuredCalls.siteAddress c)
    (StructuredCalls.exitAddress c)
  final_halt : candidate.code (StructuredCalls.exitAddress c) = Instr.halt

/-- The original compiler is a witness, without any finite-size cutoff. -/
theorem compiled_agrees {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) :
    WholeAgreement c (StructuredCalls.compiled c input output) input output := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro q
    exact StructuredCalls.compiled_site c input output q
  · exact StructuredCalls.compiled_exit c input output

/-- Local obligations cover all labels by the original site's equivalence. -/
theorem WholeAgreement.code_eq {r s : ℕ} {c : StructuredCalls.Cmd r s}
    {p : Program r s (StructuredCalls.size c + 1)}
    {input output : Fin s} (h : WholeAgreement c p input output)
    (pc : Fin (StructuredCalls.size c + 1)) :
    p.code pc = (StructuredCalls.compiled c input output).code pc := by
  obtain ⟨slot, rfl⟩ := (StructuredCalls.labelEquiv c).surjective pc
  cases slot with
  | none =>
      simpa only [StructuredCalls.exitAddress, StructuredCalls.compiled_exit]
        using h.final_halt
  | some site =>
      simpa only [StructuredCalls.siteAddress, StructuredCalls.compiled_site]
        using h.sites site

/-- All physical transitions agree, including those from interior labels. -/
theorem step_eq_of_code {r s l : ℕ} {p q : Program r s l}
    (hcode : ∀ pc, p.code pc = q.code pc) (cfg : Cfg r s l) :
    BitProgram.step p cfg = BitProgram.step q cfg := by
  change cfg.pc.map (fun pc => execInstr (p.code pc) cfg) =
    cfg.pc.map (fun pc => execInstr (q.code pc) cfg)
  simp only [hcode]

/-- Strong bidirectional refinement for arbitrary traces, not sampled states. -/
theorem trace_iff_of_code {r s l : ℕ} {p q : Program r s l}
    (hcode : ∀ pc, p.code pc = q.code pc)
    {n : ℕ} {a b : Cfg r s l} :
    BitProgram.Trace p n a b ↔ BitProgram.Trace q n a b := by
  constructor
  · intro ht
    induction ht with
    | refl state => exact .refl state
    | @cons n state mid final hstep htail ih =>
        apply SubexponentialSAT.Computation.Trace.cons
        · calc
            BitProgram.step q state = BitProgram.step p state :=
              (step_eq_of_code hcode state).symm
            _ = some mid := hstep
        · exact ih
  · intro ht
    induction ht with
    | refl state => exact .refl state
    | @cons n state mid final hstep htail ih =>
        apply SubexponentialSAT.Computation.Trace.cons
        · calc
            BitProgram.step p state = BitProgram.step q state :=
              step_eq_of_code hcode state
            _ = some mid := hstep
        · exact ih

/-- Exact transition counts and arbitrary runtime bounds are preserved. -/
theorem runsIn_iff_of_code {r s l : ℕ} {p q : Program r s l}
    (hcode : ∀ pc, p.code pc = q.code pc)
    {limit : ℕ} {a b : Cfg r s l} :
    BitProgram.RunsIn p limit a b ↔ BitProgram.RunsIn q limit a b := by
  constructor
  · rintro ⟨n, hn, ht⟩
    exact ⟨n, hn, (trace_iff_of_code hcode).mp ht⟩
  · rintro ⟨n, hn, ht⟩
    exact ⟨n, hn, (trace_iff_of_code hcode).mpr ht⟩

theorem WholeAgreement.step_eq {r s : ℕ} {c : StructuredCalls.Cmd r s}
    {p : Program r s (StructuredCalls.size c + 1)}
    {input output : Fin s} (h : WholeAgreement c p input output)
    (cfg : Cfg r s (StructuredCalls.size c + 1)) :
    BitProgram.step p cfg =
      BitProgram.step (StructuredCalls.compiled c input output) cfg :=
  step_eq_of_code h.code_eq cfg

theorem WholeAgreement.trace_iff {r s : ℕ} {c : StructuredCalls.Cmd r s}
    {p : Program r s (StructuredCalls.size c + 1)}
    {input output : Fin s} (h : WholeAgreement c p input output)
    {n : ℕ} {a b : Cfg r s (StructuredCalls.size c + 1)} :
    BitProgram.Trace p n a b ↔
      BitProgram.Trace (StructuredCalls.compiled c input output) n a b :=
  trace_iff_of_code h.code_eq

/-- Existing source semantics transfers to a generated machine via agreement. -/
theorem WholeAgreement.eval_halt_trace {r s : ℕ} {c : StructuredCalls.Cmd r s}
    {p : Program r s (StructuredCalls.size c + 1)}
    {input output : Fin s} (h : WholeAgreement c p input output)
    {n : ℕ} {a b : StructuredCalls.State r s}
    (he : StructuredCalls.Eval c n a b) :
    BitProgram.Trace p (n + 1)
      (a.withPC (some p.entry)) (b.withPC none) := by
  have sourceTrace := StructuredCalls.compiled_halt_trace he input output
  have targetTrace := (h.trace_iff).mpr sourceTrace
  rw [h.source_entry]
  exact targetTrace

end OAI.Algorithms.SubexponentialSAT.LeanRustRefinement


/-!
## Proof-producing structural source-graph lowering

A \`SourceGraph c\` carries a source-command index in its type. It cannot
silently replace a call, branch, loop guard, or callee program with a different
one. Its instruction lookup and entry function are defined *independently* of
\`StructuredCalls.code\` and \`StructuredCalls.entry\`, then related by induction.

This is a source-side semantic representation for a proof-carrying compiler.
It is not a proof that an arbitrary JSON document or generated Rust binary
faithfully serializes the source-indexed graph. The serialization boundary
must be separately checked or proved.
-/

namespace OAI.Algorithms.SubexponentialSAT.LeanRustRefinement

open BitProgram

/-- An independently interpreted source-indexed graph. A source declaration
determines the constructor and its original, fully typed operands. -/
inductive SourceGraph {r s : ℕ} :
    StructuredCalls.Cmd r s → Type where
  | base (c : StructuredProgram.Cmd r s) : SourceGraph (.base c)
  | call {labels : ℕ} (callee : Program r s labels) : SourceGraph (.call callee)
  | seq {first second : StructuredCalls.Cmd r s}
      (a : SourceGraph first) (b : SourceGraph second) :
      SourceGraph (.seq first second)
  | ite {yes no : StructuredCalls.Cmd r s} (test : Fin r)
      (a : SourceGraph yes) (b : SourceGraph no) :
      SourceGraph (.ite test yes no)
  | while {body : StructuredCalls.Cmd r s} (test : Fin r)
      (a : SourceGraph body) : SourceGraph (.while test body)

/-- Construct the graph by structural recursion over the *elaborated* source. -/
def SourceGraph.lower {r s : ℕ} :
    (c : StructuredCalls.Cmd r s) → SourceGraph c
  | .base c => .base c
  | .call p => .call p
  | .seq first second => .seq (lower first) (lower second)
  | .ite test yes no => .ite test (lower yes) (lower no)
  | .while test body => .while test (lower body)

/-- Interpret graph entry independently of the original source compiler. -/
def SourceGraph.entry {r s l : ℕ} {c : StructuredCalls.Cmd r s}
    (g : SourceGraph c) (embed : StructuredCalls.Site c → Fin l)
    (exit : Fin l) : Fin l :=
  match g with
  | .base c => StructuredProgram.entry c embed exit
  | .call p => embed p.entry
  | .seq first second =>
      entry first (embed ∘ Sum.inl)
        (entry second (embed ∘ Sum.inr) exit)
  | .ite _ _ _ => embed none
  | .while _ _ => embed none

/-- Graph code lookup is lazy: it does not allocate the full finite table.
Calls relocate their *original instructions*, including halt-to-return. -/
def SourceGraph.code {r s l : ℕ} {c : StructuredCalls.Cmd r s}
    (g : SourceGraph c) (embed : StructuredCalls.Site c → Fin l)
    (exit : Fin l) : StructuredCalls.Site c → Instr r s l :=
  match g with
  | .base c => StructuredProgram.code c embed exit
  | .call p => fun q =>
      ProgramLinking.relocateInstr id id embed (some exit) (p.code q)
  | .seq first second => fun q =>
      match q with
      | .inl x => code first (embed ∘ Sum.inl)
          (entry second (embed ∘ Sum.inr) exit) x
      | .inr x => code second (embed ∘ Sum.inr) exit x
  | .ite test yes no => fun q =>
      match q with
      | none => .branch test
          (entry yes (fun x => embed (some (.inl x))) exit)
          (entry no (fun x => embed (some (.inr x))) exit)
      | some (.inl x) =>
          code yes (fun x => embed (some (.inl x))) exit x
      | some (.inr x) =>
          code no (fun x => embed (some (.inr x))) exit x
  | .while test body => fun q =>
      match q with
      | none =>
          .branch test (entry body (embed ∘ some) (embed none)) exit
      | some x => code body (embed ∘ some) (embed none) x

/-- Entry correspondence holds for *any* embedding and exit address. -/
theorem SourceGraph.entry_correct {r s : ℕ}
    {c : StructuredCalls.Cmd r s} (g : SourceGraph c) :
    ∀ {l : ℕ} (embed : StructuredCalls.Site c → Fin l) (exit : Fin l),
      entry g embed exit = StructuredCalls.entry c embed exit := by
  induction g with
  | base c =>
      intro l embed exit
      rfl
  | call p =>
      intro l embed exit
      rfl
  | seq first second ihf ihs =>
      intro l embed exit
      change
        entry first (embed ∘ Sum.inl)
          (entry second (embed ∘ Sum.inr) exit) =
        StructuredCalls.entry _ (embed ∘ Sum.inl)
          (StructuredCalls.entry _ (embed ∘ Sum.inr) exit)
      rw [ihs, ihf]
  | ite test yes no ihy ihn =>
      intro l embed exit
      rfl
  | while test body ih =>
      intro l embed exit
      rfl

/-- Every graph instruction is the original source instruction, for *all*
sites and arbitrary embeddings, including relocated calls and loop back-edges. -/
theorem SourceGraph.code_correct {r s : ℕ}
    {c : StructuredCalls.Cmd r s} (g : SourceGraph c) :
    ∀ {l : ℕ} (embed : StructuredCalls.Site c → Fin l)
      (exit : Fin l) (q : StructuredCalls.Site c),
      code g embed exit q = StructuredCalls.code c embed exit q := by
  induction g with
  | base c =>
      intro l embed exit q
      rfl
  | call p =>
      intro l embed exit q
      rfl
  | seq first second ihf ihs =>
      intro l embed exit q
      cases q with
      | inl x =>
          change code first (embed ∘ Sum.inl)
              (entry second (embed ∘ Sum.inr) exit) x =
            StructuredCalls.code _ (embed ∘ Sum.inl)
              (StructuredCalls.entry _ (embed ∘ Sum.inr) exit) x
          rw [entry_correct second]
          exact ihf (embed ∘ Sum.inl)
            (StructuredCalls.entry _ (embed ∘ Sum.inr) exit) x
      | inr x =>
          change code second (embed ∘ Sum.inr) exit x =
            StructuredCalls.code _ (embed ∘ Sum.inr) exit x
          exact ihs (embed ∘ Sum.inr) exit x
  | ite test yes no ihy ihn =>
      intro l embed exit q
      cases q with
      | none =>
          change Instr.branch test
              (entry yes (fun x => embed (some (.inl x))) exit)
              (entry no (fun x => embed (some (.inr x))) exit) =
            Instr.branch test
              (StructuredCalls.entry _ (fun x => embed (some (.inl x))) exit)
              (StructuredCalls.entry _ (fun x => embed (some (.inr x))) exit)
          rw [entry_correct yes, entry_correct no]
      | some branch =>
          cases branch with
          | inl x =>
              change code yes (fun q => embed (some (.inl q))) exit x =
                StructuredCalls.code _ (fun q => embed (some (.inl q))) exit x
              exact ihy (fun q => embed (some (.inl q))) exit x
          | inr x =>
              change code no (fun q => embed (some (.inr q))) exit x =
                StructuredCalls.code _ (fun q => embed (some (.inr q))) exit x
              exact ihn (fun q => embed (some (.inr q))) exit x
  | while test body ih =>
      intro l embed exit q
      cases q with
      | none =>
          change Instr.branch test
              (entry body (embed ∘ some) (embed none)) exit =
            Instr.branch test
              (StructuredCalls.entry _ (embed ∘ some) (embed none)) exit
          rw [entry_correct body]
      | some x =>
          change code body (embed ∘ some) (embed none) x =
            StructuredCalls.code _ (embed ∘ some) (embed none) x
          exact ih (embed ∘ some) (embed none) x

/-- On-demand physical program from the graph, indexed by original source
labels. Uses the proved source label equivalence, not a flat array. -/
def SourceGraph.physical {r s : ℕ} {c : StructuredCalls.Cmd r s}
    (g : SourceGraph c) (input output : Fin s) :
    Program r s (StructuredCalls.size c + 1) where
  inputStack := input
  outputStack := output
  entry := entry g (StructuredCalls.siteAddress c) (StructuredCalls.exitAddress c)
  code label := match (StructuredCalls.labelEquiv c).symm label with
    | none => .halt
    | some q => code g (StructuredCalls.siteAddress c)
        (StructuredCalls.exitAddress c) q

theorem SourceGraph.physical_site {r s : ℕ}
    {c : StructuredCalls.Cmd r s} (g : SourceGraph c)
    (input output : Fin s) (q : StructuredCalls.Site c) :
    (physical g input output).code (StructuredCalls.siteAddress c q) =
      code g (StructuredCalls.siteAddress c)
        (StructuredCalls.exitAddress c) q := by
  change (match (StructuredCalls.labelEquiv c).symm
      ((StructuredCalls.labelEquiv c) (some q)) with
      | none => Instr.halt
      | some q => code g (StructuredCalls.siteAddress c)
          (StructuredCalls.exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

theorem SourceGraph.physical_exit {r s : ℕ}
    {c : StructuredCalls.Cmd r s} (g : SourceGraph c)
    (input output : Fin s) :
    (physical g input output).code (StructuredCalls.exitAddress c) =
      Instr.halt := by
  change (match (StructuredCalls.labelEquiv c).symm
      ((StructuredCalls.labelEquiv c) none) with
      | none => Instr.halt
      | some q => code g (StructuredCalls.siteAddress c)
          (StructuredCalls.exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

/-- Structural induction automatically discharges all local site obligations
and obtains the previous PR's whole-program refinement certificate. -/
theorem SourceGraph.agrees {r s : ℕ}
    {c : StructuredCalls.Cmd r s} (g : SourceGraph c)
    (input output : Fin s) :
    WholeAgreement c (physical g input output) input output := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact entry_correct g (StructuredCalls.siteAddress c)
      (StructuredCalls.exitAddress c)
  · intro q
    calc
      (physical g input output).code (StructuredCalls.siteAddress c q) =
          code g (StructuredCalls.siteAddress c)
            (StructuredCalls.exitAddress c) q :=
        physical_site g input output q
      _ = StructuredCalls.code c (StructuredCalls.siteAddress c)
          (StructuredCalls.exitAddress c) q :=
        code_correct g (StructuredCalls.siteAddress c)
          (StructuredCalls.exitAddress c) q
  · exact physical_exit g input output

/-- Every source command now has an automatically verified graph compilation.
There is no enumerated size bound and no unproved code equality hypothesis. -/
theorem SourceGraph.lower_agrees {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) :
    WholeAgreement c (physical (lower c) input output) input output :=
  agrees (lower c) input output

/-- Strong equivalence for all execution lengths and all physical states. -/
theorem SourceGraph.trace_iff {r s : ℕ}
    {c : StructuredCalls.Cmd r s} (g : SourceGraph c)
    (input output : Fin s) {n : ℕ}
    {a b : Cfg r s (StructuredCalls.size c + 1)} :
    BitProgram.Trace (physical g input output) n a b ↔
      BitProgram.Trace (StructuredCalls.compiled c input output) n a b :=
  (agrees g input output).trace_iff

/-- Existing source-level correctness proof transfers to the graph execution. -/
theorem SourceGraph.eval_halt_trace {r s : ℕ}
    {c : StructuredCalls.Cmd r s} (g : SourceGraph c)
    (input output : Fin s) {n : ℕ} {a b : StructuredCalls.State r s}
    (he : StructuredCalls.Eval c n a b) :
    BitProgram.Trace (physical g input output) (n + 1)
      (a.withPC (some (physical g input output).entry)) (b.withPC none) :=
  (agrees g input output).eval_halt_trace he

end OAI.Algorithms.SubexponentialSAT.LeanRustRefinement
