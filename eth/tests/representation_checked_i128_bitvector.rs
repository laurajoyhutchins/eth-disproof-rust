//! Independent signed-magnitude oracle for the production checked i128 boundary.
//!
//! Unlike the production implementation, the oracle never performs signed
//! addition or multiplication. It decomposes each operand into sign and
//! unsigned magnitude, performs u128 arithmetic, and reconstructs only values
//! representable in the asymmetric signed 128-bit interval.
//!
//! These are differential executable tests. Lean separately proves a
//! BitVec-128 overflow specification, not Rust compiler refinement.

use lean_eth_reference::Error;
use lean_eth_reference::representation_ranked_certificate::{
    checked_i128_add, checked_i128_mul,
};

fn magnitude_parts(value: i128) -> (bool, u128) {
    (value < 0, value.unsigned_abs())
}

fn signed_from_magnitude(negative: bool, magnitude: u128) -> Option<i128> {
    if magnitude == 0 {
        return Some(0);
    }
    if negative && magnitude == (1u128 << 127) {
        return Some(i128::MIN);
    }
    let positive = i128::try_from(magnitude).ok()?;
    Some(if negative { -positive } else { positive })
}

fn reference_add(a: i128, b: i128) -> Option<i128> {
    let (negative_a, magnitude_a) = magnitude_parts(a);
    let (negative_b, magnitude_b) = magnitude_parts(b);
    if negative_a == negative_b {
        signed_from_magnitude(negative_a, magnitude_a.checked_add(magnitude_b)?)
    } else if magnitude_a >= magnitude_b {
        signed_from_magnitude(negative_a, magnitude_a - magnitude_b)
    } else {
        signed_from_magnitude(negative_b, magnitude_b - magnitude_a)
    }
}

fn reference_mul(a: i128, b: i128) -> Option<i128> {
    let (negative_a, magnitude_a) = magnitude_parts(a);
    let (negative_b, magnitude_b) = magnitude_parts(b);
    signed_from_magnitude(
        negative_a ^ negative_b,
        magnitude_a.checked_mul(magnitude_b)?,
    )
}

fn compare_pair(a: i128, b: i128) {
    for (actual, expected) in [
        (checked_i128_add(a, b), reference_add(a, b)),
        (checked_i128_mul(a, b), reference_mul(a, b)),
    ] {
        match (actual, expected) {
            (Ok(value), Some(reference)) => assert_eq!(value, reference, "a={a}, b={b}"),
            (Err(Error::Overflow), None) => {}
            (other, reference) => {
                panic!("a={a}, b={b}: actual {other:?}, expected {reference:?}")
            }
        }
    }
}

#[test]
fn critical_asymmetric_signed_boundaries() {
    let boundary = [
        i128::MIN,
        i128::MIN + 1,
        i128::MIN / 2,
        -(1i128 << 64),
        -3,
        -2,
        -1,
        0,
        1,
        2,
        3,
        1i128 << 64,
        i128::MAX / 2,
        i128::MAX - 1,
        i128::MAX,
    ];
    for a in boundary {
        for b in boundary {
            compare_pair(a, b);
        }
    }
    assert_eq!(checked_i128_mul(i128::MIN, -1), Err(Error::Overflow));
    assert_eq!(checked_i128_mul(i128::MIN, 1), Ok(i128::MIN));
    assert_eq!(checked_i128_add(i128::MAX, 1), Err(Error::Overflow));
    assert_eq!(checked_i128_add(i128::MIN, -1), Err(Error::Overflow));
}

fn next_word(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut x = *seed;
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

fn random_i128(seed: &mut u64) -> i128 {
    let upper = next_word(seed) as u128;
    let lower = next_word(seed) as u128;
    ((upper << 64) | lower) as i128
}

#[test]
fn deterministic_full_width_signed_words_match_independent_oracle() {
    let mut seed = 0x239d_4a1b_9f15_c3e7u64;
    for _ in 0..16_384 {
        let a = random_i128(&mut seed);
        let b = random_i128(&mut seed);
        compare_pair(a, b);
    }
}

#[test]
fn zero_one_and_cancellation_match_exact_signed_arithmetic() {
    let mut seed = 0xd6e8_feb8_6659_fd93u64;
    for _ in 0..2_048 {
        let a = random_i128(&mut seed);
        compare_pair(a, 0);
        compare_pair(a, 1);
        compare_pair(a, -1);
        if a != i128::MIN {
            compare_pair(a, -a);
        }
    }
}
