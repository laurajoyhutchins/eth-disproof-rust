//! Literal ports from pinned Lean `ExecCNFSubset.subsetProgram` and
//! `ExecClauseRelationsProgram.program`.
//! All subset/equivalence/strict-subset decisions execute as finite commands.
use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_query_prefix::frame_program;
use crate::native_terminal_classifier::subset_member_call;

fn scan_records(reader: Program<10, 8>, callback: Cmd<10, 8>) -> Cmd<10, 8> {
    let advance = Cmd::ite(
        9,
        Cmd::Atom(Atom::Set {
            dst: 7,
            value: false,
        }),
        Cmd::Atom(Atom::Pop {
            stack: 0,
            value: 7,
            present: 8,
        }),
    );
    Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 9,
            value: false,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Pop {
                stack: 0,
                value: 7,
                present: 8,
            }),
            Cmd::while_(7, Cmd::seq(Cmd::Call(reader), Cmd::seq(callback, advance))),
        ),
    )
}

/// Source `ExecCNFSubset.callback` for a single decoded source literal.
pub fn subset_callback() -> Result<Cmd<10, 8>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(2, 3, 7, 0, 1)?),
        Cmd::seq(
            subset_member_call()?,
            Cmd::seq(
                Cmd::Atom(Atom::Not { dst: 9, src: 4 }),
                Cmd::seq(
                    Cmd::Call(clear_program(3, 0, 1)?),
                    Cmd::seq(
                        Cmd::Call(clear_program(4, 0, 1)?),
                        Cmd::Call(clear_program(1, 0, 1)?),
                    ),
                ),
            ),
        ),
    ))
}

/// Source `ExecCNFSubset.subset`: physical membership comparisons across all
/// literal records; the flag becomes true precisely if none are missing.
pub fn subset_command() -> Result<Cmd<10, 8>, Error> {
    let reader = frame_program()?.lift::<10, 8>([7, 8], [0, 1])?;
    let iterate = scan_records(reader, subset_callback()?);
    Ok(Cmd::seq(
        iterate,
        Cmd::seq(
            Cmd::Atom(Atom::Not { dst: 9, src: 9 }),
            Cmd::Atom(Atom::Push { stack: 1, src: 9 }),
        ),
    ))
}
pub fn subset_program() -> Result<Program<10, 8>, Error> {
    subset_command()?.compiled(0, 1)
}

/// Original `ExecClauseRelationsProgram.subsetProgram` uses identity port maps
/// (Lean Fin.castAdd), preserving the saved 8/9 stacks and 10/11 registers.
pub fn subset_lift() -> Result<Program<12, 10>, Error> {
    subset_program()?.lift::<12, 10>([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 1, 2, 3, 4, 5, 6, 7])
}

fn compare(source: usize, target: usize) -> Result<Cmd<12, 10>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(source, 0, 7, 0, 1)?),
        Cmd::seq(
            Cmd::Call(copy_program(target, 2, 7, 0, 1)?),
            Cmd::seq(
                Cmd::Call(subset_lift()?),
                Cmd::seq(
                    Cmd::Call(clear_program(0, 0, 1)?),
                    Cmd::seq(
                        Cmd::Call(clear_program(1, 0, 1)?),
                        Cmd::Call(clear_program(2, 0, 1)?),
                    ),
                ),
            ),
        ),
    ))
}

/// Real dual-direction clause relation. At exit:
/// reg9 = !subset(B,A), reg10 = equivalent(A,B),
/// reg11 = strictSubset(A,B). Both original encoded clauses are preserved.
pub fn relation_command() -> Result<Cmd<12, 10>, Error> {
    Ok(Cmd::seq(
        compare(8, 9)?,
        Cmd::seq(
            Cmd::Atom(Atom::Copy { dst: 11, src: 9 }),
            Cmd::seq(
                compare(9, 8)?,
                Cmd::seq(
                    Cmd::Atom(Atom::And {
                        dst: 10,
                        left: 11,
                        right: 9,
                    }),
                    Cmd::seq(
                        Cmd::Atom(Atom::Not { dst: 9, src: 9 }),
                        Cmd::Atom(Atom::And {
                            dst: 11,
                            left: 11,
                            right: 9,
                        }),
                    ),
                ),
            ),
        ),
    ))
}
pub fn relation_program() -> Result<Program<12, 10>, Error> {
    relation_command()?.compiled(8, 0)
}
