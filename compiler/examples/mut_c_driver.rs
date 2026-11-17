#![forbid(unsafe_code)]
// Driver only. All mathematical functions are compiled from MutKernels.lean.
use lean_generated::{unique, shared, __LeanValue};
fn main() {
    let mut args = std::env::args().skip(1);
    while let Some(left) = args.next() {
        let right = args.next().expect("expected decimal Nat pairs");
        assert!(!left.is_empty() && left.bytes().all(|x| x.is_ascii_digit()));
        assert!(!right.is_empty() && right.bytes().all(|x| x.is_ascii_digit()));
        let a = __LeanValue::nat_from_decimal(&left);
        let b = __LeanValue::nat_from_decimal(&right);
        println!("{} {}", unique(a.clone(), b.clone()).nat_to_decimal(), shared(a, b).nat_to_decimal());
    }
}
