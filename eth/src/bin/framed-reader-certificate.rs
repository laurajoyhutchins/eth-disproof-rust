//! Emit the *actual Rust-computed* frame-parser lift and compiled-call tables
//! as Lean declarations for pinned-source kernel translation validation.
//!
//! No expected instruction rows are embedded in this executable. Every
//! declaration is serialized from `Program::code()` after calling the real
//! `Program::lift` and `Cmd::compiled` implementations. The Lean checker
//! separately imports the original OpenAI source, proves full program
//! equality, and fails on any unexpected physical instruction. This remains
//! translation validation of six concrete instances, not a verified Rust
//! compiler nor an unconditional proof about this serializer.

use std::fmt::Write;

use lean_eth_reference::bit_program::frame_programs::frame_program;
use lean_eth_reference::bit_program::{Cmd, Instr, Program};

/// A total formatter for the current finite instruction vocabulary.
/// Unknown future opcode variants must cause a compiler error, not be skipped.
fn instruction_lean(instruction: &Instr) -> String {
    match *instruction {
        Instr::Halt => ".halt".into(),
        Instr::Goto { next } => format!(".goto {next}"),
        Instr::Set { dst, value, next } => {
            format!(".set {dst} {} {next}", if value { "true" } else { "false" })
        }
        Instr::Copy { dst, src, next } => format!(".copy {dst} {src} {next}"),
        Instr::Not { dst, src, next } => format!(".bnot {dst} {src} {next}"),
        Instr::And {
            dst,
            left,
            right,
            next,
        } => format!(".band {dst} {left} {right} {next}"),
        Instr::Or {
            dst,
            left,
            right,
            next,
        } => format!(".bor {dst} {left} {right} {next}"),
        Instr::Xor {
            dst,
            left,
            right,
            next,
        } => format!(".bxor {dst} {left} {right} {next}"),
        Instr::Branch { test, yes, no } => format!(".branch {test} {yes} {no}"),
        Instr::Push { stack, src, next } => format!(".push {stack} {src} {next}"),
        Instr::Peek {
            stack,
            value,
            present,
            next,
        } => format!(".peek {stack} {value} {present} {next}"),
        Instr::Pop {
            stack,
            value,
            present,
            next,
        } => format!(".pop {stack} {value} {present} {next}"),
    }
}

/// Serialize the fields and *all* labels, not an inferred or handwritten
/// source formula. The final wildcard is safe because Program owns a
/// validated table of exactly the declared length.
fn program_lean<const R: usize, const S: usize>(
    output: &mut String,
    name: &str,
    program: &Program<R, S>,
) {
    writeln!(
        output,
        "private def {name} : Program {R} {S} {} where",
        program.code().len()
    )
    .unwrap();
    writeln!(output, "  inputStack := {}", program.input_stack()).unwrap();
    writeln!(output, "  outputStack := {}", program.output_stack()).unwrap();
    writeln!(output, "  entry := {}", program.entry()).unwrap();
    writeln!(output, "  code pc := match pc.val with").unwrap();

    for (index, instr) in program.code().iter().enumerate() {
        let label = if index + 1 == program.code().len() {
            "_".to_string()
        } else {
            index.to_string()
        };
        writeln!(output, "    | {label} => {}", instruction_lean(instr)).unwrap();
    }
}

#[derive(Clone, Copy)]
struct Ports {
    tag: usize,
    present: usize,
    found: usize,
    source: usize,
    payload: usize,
    input: usize,
    output: usize,
}

fn checked_ports<const R: usize, const S: usize>(
    ports: Ports,
) -> Result<(), Box<dyn std::error::Error>> {
    if ports.tag >= R
        || ports.present >= R
        || ports.found >= R
        || ports.tag == ports.present
        || ports.tag == ports.found
        || ports.present == ports.found
        || ports.source >= S
        || ports.payload >= S
        || ports.source == ports.payload
        || ports.input >= S
        || ports.output >= S
    {
        return Err("invalid source RecordPrograms.Ports or compiled I/O port".into());
    }
    Ok(())
}

/// Build the two actual programs and produce their kernel-checkable
/// assertions against independently defined Lean source programs.
fn case<const R: usize, const S: usize>(
    name: &str,
    ports: Ports,
) -> Result<String, Box<dyn std::error::Error>> {
    checked_ports::<R, S>(ports)?;
    let lifted =
        frame_program()?.lift::<R, S>([ports.tag, ports.present], [ports.source, ports.payload])?;
    let compiled = Cmd::Call(lifted.clone()).compiled(ports.input, ports.output)?;

    let mut out = String::new();
    writeln!(
        out,
        "private def ports_{name} : RecordPrograms.Ports {R} {S} where"
    )?;
    writeln!(out, "  tag := {}", ports.tag)?;
    writeln!(out, "  present := {}", ports.present)?;
    writeln!(out, "  found := {}", ports.found)?;
    writeln!(out, "  source := {}", ports.source)?;
    writeln!(out, "  payload := {}", ports.payload)?;
    writeln!(out, "  tag_ne_present := by decide")?;
    writeln!(out, "  found_ne_tag := by decide")?;
    writeln!(out, "  found_ne_present := by decide")?;
    writeln!(out, "  source_ne_payload := by decide")?;

    program_lean(&mut out, &format!("rust_lift_{name}"), &lifted);
    program_lean(&mut out, &format!("rust_compiled_{name}"), &compiled);

    // These theorems make each actual serialized Rust table answer to the
    // pinned original. The equality of the manually stated general *Lean*
    // table with the original source was separately established above.
    writeln!(
        out,
        "private theorem rust_lift_{name}_eq : rust_lift_{name} = mappedFrameProgram ports_{name} := by"
    )?;
    writeln!(out, "  apply program_eq_of_fields")?;
    writeln!(out, "  · rfl\n  · rfl\n  · rfl")?;
    writeln!(out, "  · intro pc\n    fin_cases pc <;> rfl")?;

    writeln!(
        out,
        "private theorem rust_compiled_{name}_eq : rust_compiled_{name} = mappedCompiledFrameProgram ports_{name} {} {} := by",
        ports.input, ports.output
    )?;
    writeln!(out, "  apply program_eq_of_fields")?;
    writeln!(out, "  · rfl\n  · rfl\n  · rfl")?;
    writeln!(out, "  · intro pc\n    fin_cases pc <;> rfl")?;

    writeln!(
        out,
        "theorem rust_lift_{name}_source : rust_lift_{name} = ProgramLinking.liftProgram ParserProgram.frameProgram (RecordPrograms.registerMap ports_{name}) (RecordPrograms.stackMap ports_{name}) := by"
    )?;
    writeln!(
        out,
        "  rw [rust_lift_{name}_eq, mappedFrameProgram_eq_source]"
    )?;
    writeln!(
        out,
        "theorem rust_compiled_{name}_source : rust_compiled_{name} = StructuredCalls.compiled (.call (mappedFrameProgram ports_{name})) {} {} := by",
        ports.input, ports.output
    )?;
    writeln!(
        out,
        "  rw [rust_compiled_{name}_eq, mappedCompiledFrameProgram_eq_source]"
    )?;
    Ok(out)
}

fn certificate() -> Result<String, Box<dyn std::error::Error>> {
    let mut result = String::from(
        "\nnamespace OAI.Algorithms.SubexponentialSAT.LeanRustRefinement\n\nopen BitProgram\n",
    );

    // These six entries are the actual caller ABIs. Dedup and self-filter
    // share the frame lift but deliberately retain distinct output ports.
    let examples = [
        case::<15, 16>(
            "dedup",
            Ports {
                tag: 0,
                present: 1,
                found: 14,
                source: 13,
                payload: 15,
                input: 13,
                output: 13,
            },
        )?,
        case::<15, 16>(
            "filter",
            Ports {
                tag: 0,
                present: 1,
                found: 14,
                source: 13,
                payload: 15,
                input: 13,
                output: 15,
            },
        )?,
        case::<15, 12>(
            "relation",
            Ports {
                tag: 12,
                present: 13,
                found: 14,
                source: 10,
                payload: 11,
                input: 10,
                output: 11,
            },
        )?,
        case::<13, 11>(
            "tautology",
            Ports {
                tag: 10,
                present: 11,
                found: 12,
                source: 0,
                payload: 1,
                input: 0,
                output: 0,
            },
        )?,
        case::<7, 5>(
            "membership",
            Ports {
                tag: 5,
                present: 6,
                found: 4,
                source: 0,
                payload: 1,
                input: 0,
                output: 1,
            },
        )?,
        case::<3, 4>(
            "reversal",
            Ports {
                tag: 0,
                present: 1,
                found: 2,
                source: 0,
                payload: 3,
                input: 0,
                output: 2,
            },
        )?,
    ];
    for example in examples {
        result.push_str(&example);
        result.push('\n');
    }
    result.push_str("end OAI.Algorithms.SubexponentialSAT.LeanRustRefinement\n");
    Ok(result)
}

fn main() {
    match certificate() {
        Ok(value) => print!("{value}"),
        Err(error) => {
            eprintln!("frame-reader certificate refusal: {error}");
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_receipt_serializes_the_actual_relocated_halt_and_full_ports() {
        let value = certificate().unwrap();
        assert_eq!(value.matches("private def rust_lift_").count(), 6);
        assert_eq!(value.matches("private def rust_compiled_").count(), 6);
        assert_eq!(value.matches("theorem rust_compiled_").count(), 6);
        assert!(value.contains("    | _ => .goto 0"));
        assert!(value.contains("  entry := 1"));
        assert!(value.contains("  entry := 0"));
        assert!(value.contains("  found_ne_present := by decide"));
    }

    #[test]
    fn serializer_does_not_silently_omit_or_normalize_a_changed_instruction() {
        let baseline = Program::<3, 4>::new(
            0,
            1,
            0,
            vec![
                Instr::Set {
                    dst: 2,
                    value: true,
                    next: 1,
                },
                Instr::Halt,
            ],
        )
        .unwrap();
        let changed = Program::<3, 4>::new(
            0,
            1,
            0,
            vec![
                Instr::Set {
                    dst: 2,
                    value: false,
                    next: 1,
                },
                Instr::Halt,
            ],
        )
        .unwrap();
        let mut a = String::new();
        let mut b = String::new();
        program_lean(&mut a, "actual", &baseline);
        program_lean(&mut b, "actual", &changed);
        assert_ne!(a, b);
        assert!(a.contains(".set 2 true 1"));
        assert!(b.contains(".set 2 false 1"));
    }

    #[test]
    fn source_forbidden_found_alias_is_refused_before_certificate_output() {
        let invalid = Ports {
            tag: 0,
            present: 1,
            found: 0,
            source: 0,
            payload: 1,
            input: 0,
            output: 1,
        };
        assert!(case::<3, 3>("invalid", invalid).is_err());
    }
}
