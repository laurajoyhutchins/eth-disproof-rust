//! Fixed-width H-cache normalization, ported from the actual Lean machine.
//!
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! `ModularPrograms.paddingProgram`, `ModularRingPrograms.normalizeProgram`,
//! `LayoutProgramNormalize.normalizeAt`, and
//! `LayoutBinomialProgram.normalizeComponent`.
//!
//! The 12-label table below is `link (link padding clear) transfer`, not an
//! atomic Rust vector operation. The caller uses the source's physical 8x9
//! register/stack maps, the scratch stack and its two paid calls.
use crate::Error;
use crate::bit_program::{Cmd, Instr, Program};
use crate::native_high::copy_program;
use crate::native_query_prefix::transfer_program;

/// Exact 12-label `ModularRingPrograms.normalizeProgram` including its linked
/// clear of the entire *excess* input, preserving long-input semantics.
pub fn normalize_program() -> Result<Program<8, 8>, Error> {
    Program::new(
        0,
        0,
        0,
        vec![
            // paddingProgram, lifted by normalizePorts [7,0,2].
            Instr::Pop {
                stack: 7,
                value: 1,
                present: 3,
                next: 1,
            },
            Instr::Branch {
                test: 3,
                yes: 2,
                no: 4,
            },
            Instr::Pop {
                stack: 0,
                value: 2,
                present: 4,
                next: 3,
            },
            Instr::Push {
                stack: 2,
                src: 2,
                next: 0,
            },
            Instr::Goto { next: 5 },
            // clearProgram 0 1 3 (linked halt -> transfer entry).
            Instr::Pop {
                stack: 0,
                value: 1,
                present: 3,
                next: 6,
            },
            Instr::Branch {
                test: 3,
                yes: 5,
                no: 7,
            },
            Instr::Goto { next: 8 },
            // transferProgram 2 0 1 3.
            Instr::Pop {
                stack: 2,
                value: 1,
                present: 3,
                next: 9,
            },
            Instr::Branch {
                test: 3,
                yes: 10,
                no: 11,
            },
            Instr::Push {
                stack: 0,
                src: 1,
                next: 8,
            },
            Instr::Halt,
        ],
    )
}

/// Source `LayoutBinomialProgram.normalizePorts` inside its 9-stack component.
/// Local normalize ports [0,1,2,3,4,5,6,7] map to [0,4,5,6,7,2,8,3].
pub const COMPONENT_PORTS: [usize; 8] = [0, 4, 5, 6, 7, 2, 8, 3];

/// `normalizeComponent`: preserve a copy of runtime width, normalize the raw
/// coefficient in little-endian order, then prepend its *reversed* fixed-width
/// representation to the accumulated output buffer.
pub fn normalize_component_command() -> Result<Cmd<8, 9>, Error> {
    let normalize =
        normalize_program()?.lift::<8, 9>(std::array::from_fn(|i| i), COMPONENT_PORTS)?;
    Ok(Cmd::seq(
        Cmd::Call(copy_program(1, 3, 4, 0, 1)?),
        Cmd::seq(
            Cmd::Call(normalize),
            Cmd::Call(transfer_program(0, 2, 0, 1)?),
        ),
    ))
}

pub fn normalize_component_program() -> Result<Program<8, 9>, Error> {
    normalize_component_command()?.compiled(0, 2)
}

/// Exact `Eval normalizeComponent` cost plus one final compiled halt, given the
/// source's empty-work precondition. All arithmetic is checked.
pub fn expected_compiled_steps(width: usize, input_len: usize) -> Result<u64, Error> {
    let width = u64::try_from(width).map_err(|_| Error::Overflow)?;
    let excess =
        u64::try_from(input_len.saturating_sub(width as usize)).map_err(|_| Error::Overflow)?;
    width
        .checked_mul(17)
        .and_then(|n| excess.checked_mul(2).and_then(|e| n.checked_add(e)))
        .and_then(|n| n.checked_add(18))
        .ok_or(Error::Overflow)
}

/// Physical `RowSelectionProgram.parsePair` as used by the flat adapter.
/// The earlier source implementation is available independently in the
/// H-cache iteration module; keeping this compilation here permits direct
/// testing of the complete 8x19 flattening command in isolation.
fn parse_pair_command() -> Result<Cmd<8, 16>, Error> {
    use crate::bit_program::Atom;
    use crate::native_query_prefix::frame_program;
    let positive = frame_program()?.lift::<8, 16>([0, 1], [15, 2])?;
    let negative = frame_program()?.lift::<8, 16>([0, 1], [15, 3])?;
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Pop {
            stack: 15,
            value: 7,
            present: 6,
        }),
        Cmd::ite(
            7,
            Cmd::seq(Cmd::Call(positive), Cmd::Call(negative)),
            Cmd::Skip,
        ),
    ))
}

/// `LayoutBinomialProgram.flatParse`: one compiled `parse` command, itself a
/// lifted compiled `parsePair`, then a second lift into the wide bank. The
/// extra compiled calls are part of the source instruction accounting.
pub fn flat_parse_command() -> Result<Cmd<8, 19>, Error> {
    let pair = parse_pair_command()?
        .compiled(0, 1)?
        .lift::<8, 18>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?;
    let parse = Cmd::Call(pair);
    let wide = parse
        .compiled(15, 15)?
        .lift::<8, 19>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?;
    Ok(Cmd::Call(wide))
}

/// Source `LayoutBinomialProgram.positivePorts` and `negativePorts`. The width
/// is retained at global port 18; positive/negative outputs at 16/17.
pub const POSITIVE_PORTS: [usize; 9] = [2, 18, 16, 4, 5, 6, 7, 8, 9];
pub const NEGATIVE_PORTS: [usize; 9] = [3, 18, 17, 4, 5, 6, 7, 8, 9];

pub fn flat_positive_command() -> Result<Cmd<8, 19>, Error> {
    let inner = normalize_component_command()?.compiled(0, 2)?;
    Ok(Cmd::Call(inner.lift::<8, 19>(
        std::array::from_fn(|i| i),
        POSITIVE_PORTS,
    )?))
}

pub fn flat_negative_command() -> Result<Cmd<8, 19>, Error> {
    let inner = normalize_component_command()?.compiled(0, 2)?;
    Ok(Cmd::Call(inner.lift::<8, 19>(
        std::array::from_fn(|i| i),
        NEGATIVE_PORTS,
    )?))
}

/// Real `LayoutBinomialProgram.flatRow`. Every signed pair is physically parsed,
/// normalized twice and appended into the two output accumulators.
pub fn flat_row_command() -> Result<Cmd<8, 19>, Error> {
    let parse = flat_parse_command()?;
    Ok(Cmd::seq(
        parse.clone(),
        Cmd::while_(
            7,
            Cmd::seq(
                flat_positive_command()?,
                Cmd::seq(flat_negative_command()?, parse),
            ),
        ),
    ))
}

/// Source `flatFinish` reverses both output accumulators by consuming them
/// with the two four-label transfer programs.
pub fn flat_finish_command() -> Result<Cmd<8, 19>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(transfer_program(16, 0, 0, 1)?),
        Cmd::Call(transfer_program(17, 1, 0, 1)?),
    ))
}

/// Complete `LayoutBinomialProgram.flatProgram` at the exact 8x19 ports.
/// This executes fixed-width flattening but does not construct the H row.
pub fn flat_program() -> Result<Program<8, 19>, Error> {
    Cmd::seq(flat_row_command()?, flat_finish_command()?).compiled(15, 0)
}
