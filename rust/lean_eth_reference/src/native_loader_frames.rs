//! Source-defined address import and matrix export at the signature-head ABI.
//!
//! `openai/math@4eaee87548250b2682affda7d05d947c05554bae`:
//! `SqrtLogSpace/SignatureHeadLoaderCore.lean`, lines 623-642 and 904-922.
//! These are real stack-copy/clear instructions, not a stand-in for the
//! unported `SignatureHeadLoader.localProgram` (matrix/head computation).
use crate::Error;
use crate::bit_program::{Cmd, Program};
use crate::native_high::{clear_program, copy_program};

const ADDRESS_CLEARS: [usize; 4] = [649, 659, 846, 847];
const EXPORT_CLEARS: [usize; 3] = [668, 669, 846];

fn clear_many(ports: &[usize]) -> Result<Cmd<16, 896>, Error> {
    // Lean's clearMany builds nested left-to-right sequences, ending in skip.
    let mut out = Cmd::Skip;
    for &port in ports.iter().rev() {
        out = Cmd::seq(Cmd::Call(clear_program(port, 0, 1)?), out);
    }
    Ok(out)
}

/// `SignatureHeadLoader.importAddressFrom(src)`. The proof's source-frame
/// precondition requires `src` distinct from all four cleaned destinations.
/// We enforce it rather than claiming preservation on an aliased source.
pub fn import_address_from_command(src: usize) -> Result<Cmd<16, 896>, Error> {
    if ADDRESS_CLEARS.contains(&src) {
        return Err(Error::Invalid(
            "signature address source overlaps a cleared stack".into(),
        ));
    }
    Ok(Cmd::seq(
        clear_many(&ADDRESS_CLEARS)?,
        Cmd::Call(copy_program(src, 649, 659, 0, 1)?),
    ))
}

pub fn import_address_from_program(src: usize) -> Result<Program<16, 896>, Error> {
    import_address_from_command(src)?.compiled(src, 649)
}

/// `SignatureHeadLoader.exportMatrix`: clear temporary 659, preserving-copy
/// the computed matrix 668 to 847, then clear sources 668,669 and index 846.
/// Destination 847 is *appended to*, unless importAddress has cleared it.
pub fn export_matrix_command() -> Result<Cmd<16, 896>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(clear_program(659, 0, 1)?),
        Cmd::seq(
            Cmd::Call(copy_program(668, 847, 659, 0, 1)?),
            clear_many(&EXPORT_CLEARS)?,
        ),
    ))
}

pub fn export_matrix_program() -> Result<Program<16, 896>, Error> {
    export_matrix_command()?.compiled(668, 847)
}

/// Source register lift `leafRegs : Fin 16 ↪ Fin 40`, identity stack map.
/// These lifted snippets are *not* `SignatureHeadLoader.programFrom`, which
/// also invokes the substantial as-yet-unported `localProgram`.
pub fn import_address_leaf_command(src: usize) -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(
        import_address_from_program(src)?
            .lift::<40, 896>(std::array::from_fn(|i| i + 24), std::array::from_fn(|i| i))?,
    ))
}

pub fn export_matrix_leaf_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(export_matrix_program()?.lift::<40, 896>(
        std::array::from_fn(|i| i + 24),
        std::array::from_fn(|i| i),
    )?))
}
