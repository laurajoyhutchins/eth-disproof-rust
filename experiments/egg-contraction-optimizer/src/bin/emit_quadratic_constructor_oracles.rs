//! Emit raw input and actual native constructor result as independent
//! data-only Lean propositions. This is finite cross-implementation
//! evidence; the universal proof concerns the Lean finite-set model.

use egg_contraction_experiment::signed_affine::QuadraticPhase;

fn indices(values: &[usize]) -> String {
    format!(
        "[{}]",
        values.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")
    )
}

fn terms(raw: &[Vec<usize>]) -> String {
    format!(
        "[{}]",
        raw.iter().map(|term| indices(term)).collect::<Vec<_>>().join(", ")
    )
}

fn emit(width: usize, raw: Vec<Vec<usize>>) {
    // Serialize the unmodified source *before* native normalization.
    let input = terms(&raw);
    let result = match QuadraticPhase::new(width, raw) {
        Err(_) => "none".to_string(),
        Ok(phase) => {
            let normalized = phase.terms().iter().cloned().collect::<Vec<_>>();
            format!(
                "some ((({} : List (List Nat)).map List.toFinset).toFinset)",
                terms(&normalized)
            )
        }
    };
    println!(
        "example : IndependentETH.QuadraticLowWeight.nativeConstruct {width} \
         ({input} : List (List Nat)) = {result} := by decide"
    );
}

fn next(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
    *seed
}

fn main() {
    for (width, raw) in [
        (0, vec![]),
        (0, vec![vec![]]),
        (0, vec![vec![0]]),
        (1, vec![vec![0, 0]]),
        (1, vec![vec![1]]),
        (2, vec![vec![0, 1], vec![1, 0]]),
        (2, vec![vec![0, 0], vec![0], vec![]]),
        (3, vec![vec![0, 1, 2]]),
        (3, vec![vec![0, 0, 1, 1]]),
        (5, vec![vec![4, 3, 4, 3], vec![2, 1], vec![1, 2], vec![]]),
        (130, vec![vec![129, 129], vec![0, 129]]),
        (130, vec![vec![130]]),
        (usize::MAX, vec![vec![usize::MAX]]),
    ] {
        emit(width, raw);
    }

    // Mixed accepted and refused cases, with a reproducible full-width
    // generator. The oracle does not enumerate all Boolean assignments.
    let mut seed = 0x20_26_11_20_a5_16_u64;
    for width in 0..=5 {
        for _case in 0..4 {
            let mut raw = Vec::new();
            let count = (next(&mut seed) % 5) as usize;
            for _ in 0..count {
                let mut term = Vec::new();
                let len = (next(&mut seed) % 5) as usize;
                for _ in 0..len {
                    // Occasionally introduce out-of-range coordinates.
                    let bound = if next(&mut seed) & 1 == 0 {
                        width.max(1)
                    } else {
                        width + 2
                    };
                    term.push((next(&mut seed) as usize) % bound);
                }
                raw.push(term);
            }
            emit(width, raw);
        }
    }
}
