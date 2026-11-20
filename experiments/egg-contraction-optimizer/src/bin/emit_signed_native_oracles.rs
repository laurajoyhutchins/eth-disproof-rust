//! Emit executable Lean checker examples from the native signed verifier.
 //! The Lean kernel accepts or rejects explicit integer-valued source/output
 //! semantics independently; this generator is not itself trusted by Lean.
use egg_contraction_experiment::affine::{AffineRegion, Equation};
use egg_contraction_experiment::signed_affine::{QuadraticPhase, SignedOneBitRegion};

fn main() {
    for forced in [false, true] {
        if let Err(error) = emit(forced) {
            eprintln!("signed native Lean fixture refused: {error}");
            std::process::exit(1);
        }
    }
}

fn emit(forced: bool) -> Result<(), String> {
    let source = SignedOneBitRegion {
        affine: AffineRegion {
            internal: vec!["x".to_owned()],
            boundary: vec!["b".to_owned()],
            equations: if forced {
                vec![Equation {
                    variables: vec!["x".to_owned(), "b".to_owned()],
                    rhs: true,
                }]
            } else {
                vec![]
            },
        },
        phase: QuadraticPhase::new(2, vec![vec![0, 1]])?,
        exponent: 0,
    };
    let (output, certificate) = source.eliminate_with_certificate()?;
    let lean = source.lean_oracle_example(&output, &certificate, 4)?;
    println!("{lean}");
    Ok(())
}
