//! Emit a reproducible Lean proof obligation for observed calls to the
//! production checked-i128 helpers. The receipt outcomes are untrusted;
//! ACC.ArithmeticReceipts independently checks them with BitVec 128.
use lean_eth_reference::representation_ranked_certificate::{
    ArithmeticKind, ArithmeticReceipt, observe_checked_arithmetic,
};

const BOUNDARY: [(i128, i128); 15] = [
    (i128::MIN, -1),
    (i128::MIN, 1),
    (i128::MIN, 0),
    (i128::MIN, i128::MAX),
    (i128::MAX, 1),
    (i128::MAX, 0),
    (i128::MAX, -1),
    (i128::MAX, 2),
    (-1, -1),
    (-1, 1),
    (0, 0),
    (1, 1),
    (2, 3),
    (i128::MIN / 2, 2),
    (i128::MAX / 2, 2),
];

fn next_word(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut value = *seed;
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn next_i128(seed: &mut u64) -> i128 {
    let upper = next_word(seed) as u128;
    let lower = next_word(seed) as u128;
    ((upper << 64) | lower) as i128
}

fn observations() -> Vec<ArithmeticReceipt> {
    let mut result = Vec::new();
    for (left, right) in BOUNDARY {
        result.push(observe_checked_arithmetic(ArithmeticKind::Add, left, right));
        result.push(observe_checked_arithmetic(ArithmeticKind::Mul, left, right));
    }
    // Both successful and overflowing full-width operations occur.
    let mut seed = 0x239d_4a1b_9f15_c3e7u64;
    for i in 0..12 {
        let left = next_i128(&mut seed);
        let right = next_i128(&mut seed);
        let right = if i % 3 == 0 { 0 } else { right };
        result.push(observe_checked_arithmetic(ArithmeticKind::Add, left, right));
        result.push(observe_checked_arithmetic(ArithmeticKind::Mul, left, right));
    }
    result
}

fn emit_lean(receipts: &[ArithmeticReceipt]) {
    println!("import ACC.ArithmeticReceipts");
    println!("open ACC.ArithmeticReceipts");
    println!("set_option maxRecDepth 4096");
    println!("set_option maxHeartbeats 2000000");
    println!("def observedReceipts : List Receipt := [");
    for (index, receipt) in receipts.iter().enumerate() {
        let kind = match receipt.kind {
            ArithmeticKind::Add => ".add",
            ArithmeticKind::Mul => ".mul",
        };
        let observed = match receipt.observed {
            Some(value) => format!("some (BitVec.ofInt 128 ({value} : ℤ))"),
            None => "none".to_owned(),
        };
        let end = if index + 1 == receipts.len() { "" } else { "," };
        println!(
            "  {{ kind := {kind}, left := BitVec.ofInt 128 ({} : ℤ), right := BitVec.ofInt 128 ({} : ℤ), observed := {observed} }}{end}",
            receipt.left, receipt.right
        );
    }
    println!("]");
    // This is rejected by Lean when even one reported outcome disagrees.
    println!("example : checkTrace observedReceipts = true := by decide");
}

fn main() {
    let receipts = observations();
    emit_lean(&receipts);
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn deterministic_fixture_includes_success_and_refusal() {
        let receipts = observations();
        assert_eq!(receipts.len(), 54);
        for kind in [ArithmeticKind::Add, ArithmeticKind::Mul] {
            assert!(
                receipts
                    .iter()
                    .any(|r| r.kind == kind && r.observed.is_none())
            );
            assert!(
                receipts
                    .iter()
                    .any(|r| r.kind == kind && r.observed.is_some())
            );
        }
        assert!(receipts.iter().any(|r| {
            r.kind == ArithmeticKind::Mul
                && r.left == i128::MIN
                && r.right == -1
                && r.observed.is_none()
        }));
    }
}
