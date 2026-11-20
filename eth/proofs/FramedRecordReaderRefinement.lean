import OAI.Algorithms.SubexponentialSAT.RecordPrograms

/-!
# Exact framed-reader boundary from the pinned original source

Pin: openai/math@4eaee87548250b2682affda7d05d947c05554bae.
Original declarations: ParserProgram.frameProgram, RecordPrograms.reader,
RecordPrograms.registerMap, RecordPrograms.stackMap and reader_eval.

The seven physical instructions below are spelled out independently of the
original ProgramLinking.liftProgram. We prove that this explicit table equals
the original source reader at *all labels* for every valid Lean Ports, then
reuse the source's exact trace and compiler theorem. Neither that equality nor
the source trace proves a Rust decoder, compiler, or binary correct.
-/

namespace OAI.Algorithms.SubexponentialSAT.LeanRustRefinement

open BitProgram

/-- Explicit Rust-shaped finite reader table. The physical register and stack
indices, ports, entry, full seven-label control graph and final halt are part
of the source-correspondence contract. -/
def mappedFrameProgram {r s : ℕ} (p : RecordPrograms.Ports r s) :
    Program r s 7 where
  inputStack := p.source
  outputStack := p.payload
  entry := 0
  code pc := match pc.val with
    | 0 => .pop p.source p.tag p.present 1
    | 1 => .branch p.present 2 6
    | 2 => .branch p.tag 3 6
    | 3 => .pop p.source p.tag p.present 4
    | 4 => .branch p.present 5 6
    | 5 => .push p.payload p.tag 0
    | _ => .halt

private theorem program_eq_of_fields {r s l : ℕ} (a b : Program r s l)
    (hi : a.inputStack = b.inputStack)
    (ho : a.outputStack = b.outputStack)
    (he : a.entry = b.entry)
    (hc : ∀ pc, a.code pc = b.code pc) : a = b := by
  cases a with
  | mk ai ao ae ac =>
    cases b with
    | mk bi bo be bc =>
      dsimp at hi ho he hc
      cases hi
      cases ho
      cases he
      have htable : ac = bc := funext hc
      cases htable
      rfl

/-- A single Lean theorem covers arbitrary valid source port mappings and
every instruction, including previously unexecuted labels and the halt. -/
theorem mappedFrameProgram_eq_source {r s : ℕ} (p : RecordPrograms.Ports r s) :
    mappedFrameProgram p =
      ProgramLinking.liftProgram ParserProgram.frameProgram
        (RecordPrograms.registerMap p) (RecordPrograms.stackMap p) := by
  apply program_eq_of_fields
  · rfl
  · rfl
  · rfl
  · intro pc
    fin_cases pc <;> rfl

/-- The original source reader is exactly the explicit program call. -/
theorem mappedFrame_reader_eq {r s : ℕ} (p : RecordPrograms.Ports r s) :
    RecordPrograms.reader p = StructuredCalls.Cmd.call (mappedFrameProgram p) := by
  change StructuredCalls.Cmd.call
    (ProgramLinking.liftProgram ParserProgram.frameProgram
      (RecordPrograms.registerMap p) (RecordPrograms.stackMap p)) = _
  rw [← mappedFrameProgram_eq_source p]

/-- The original unbounded reader execution theorem applies to the explicit
seven-label table: reversed payload, exact unread suffix, unchanged found bit,
and exactly 6*n+4 source instruction transitions. -/
theorem mappedFrame_reader_eval {r s : ℕ} (p : RecordPrograms.Ports r s)
    (base : StructuredCalls.State r s)
    (bits tail out : List Bool) (v pr f : Bool) :
    StructuredCalls.Eval (.call (mappedFrameProgram p)) (6 * bits.length + 4)
      (RecordPrograms.state p base v pr f (Encoding.frame bits ++ tail) out)
      (RecordPrograms.state p base false true f tail (bits.reverse ++ out)) := by
  rw [← mappedFrame_reader_eq p]
  exact RecordPrograms.reader_eval p base bits tail out v pr f

/-- Compiling a structured Call adds one final halt after the 6*n+4 source
reader instructions. This theorem is Lean-to-Lean and does not claim Rust
execution, heap memory, or primitive TM2 correspondence. -/
theorem mappedFrame_compiled_halt_trace {r s : ℕ}
    (p : RecordPrograms.Ports r s)
    (base : StructuredCalls.State r s)
    (bits tail out : List Bool) (v pr f : Bool)
    (input output : Fin s) :
    BitProgram.Trace
      (StructuredCalls.compiled (.call (mappedFrameProgram p)) input output)
      ((6 * bits.length + 4) + 1)
      ((RecordPrograms.state p base v pr f (Encoding.frame bits ++ tail) out).withPC
        (some (StructuredCalls.compiled (.call (mappedFrameProgram p)) input output).entry))
      ((RecordPrograms.state p base false true f tail (bits.reverse ++ out)).withPC
        none) :=
  StructuredCalls.compiled_halt_trace
    (mappedFrame_reader_eval p base bits tail out v pr f) input output

end OAI.Algorithms.SubexponentialSAT.LeanRustRefinement
