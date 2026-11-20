//! Emit a source-complete signed-CSR counting certificate for Lean.
//!
//! The Rust recognizer is *not* trusted as a proof. The emitted, explicit
//! canonical CSR and candidate receipt are independently rechecked by the
//! pinned Lean reference verifier and its kernel-checked soundness theorem.
//! Usage: cargo run -p lean-eth-reference --example emit_nonaffine_csr_certificate -- file.cnf

use lean_eth_reference::{
    parse_dimacs,
    structured_cnf::{OwnedSignedCsr, recognize_cnf},
};
use std::{error::Error, fmt::Display, fs, io};

fn list<T: Display>(values: &[T]) -> String {
    let values = values.iter().map(ToString::to_string).collect::<Vec<_>>();
    format!("[{}]", values.join(", "))
}

fn mask_source(mask: u8) -> String {
    let states = (0..8)
        .filter(|&seed| mask & (1u8 << seed) != 0)
        .map(|seed| format!("({}, {}, {})", seed & 1 != 0, seed & 2 != 0, seed & 4 != 0))
        .collect::<Vec<_>>();
    if states.is_empty() {
        "∅".to_string()
    } else {
        format!("{{{}}}", states.join(", "))
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args_os().skip(1);
    let path = args.next().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "expected one DIMACS CNF file path",
        )
    })?;
    if args.next().is_some() {
        return Err(
            io::Error::new(io::ErrorKind::InvalidInput, "unexpected extra arguments").into(),
        );
    }

    let source = fs::read_to_string(path)?;
    let cnf = parse_dimacs(&source)?;
    let receipt = recognize_cnf(&cnf)?;
    let csr = OwnedSignedCsr::from_cnf(&cnf);

    // Print no certificate on failure. Every emitted field is a bounded
    // integer or Boolean, never an unescaped source-level expression.
    println!("\n-- Rust-generated normalized-CSR certificate, independently rechecked by Lean.");
    println!("open IndependentETH.NonAffine");
    println!("private def emittedCsr : SignedCsrInput where");
    println!("  variableCount := {}", csr.variables);
    println!("  offsets := {}", list(&csr.row_offsets));
    println!("  columns := {}", list(&csr.column_indices));
    println!("  signs := {}", list(&csr.signs));
    let rhs = receipt
        .rhs
        .iter()
        .map(|&bit| if bit { "true" } else { "false" })
        .collect::<Vec<_>>();
    println!("private def emittedRhs : List Bool := {}", list(&rhs));
    println!(
        "private def emittedMask : Finset State := {}",
        mask_source(receipt.forbidden_seeds)
    );
    println!(
        "example : verifyCsrCount emittedCsr emittedRhs emittedMask = some {} := by\n  decide",
        receipt.count()
    );
    println!(
        "example : Nat.card (DecodedCsrWords emittedCsr emittedRhs) = {} := by\n  apply verifiedCsr_decodedWordCount emittedCsr emittedRhs emittedMask {}\n  decide",
        receipt.count(),
        receipt.count()
    );
    Ok(())
}
