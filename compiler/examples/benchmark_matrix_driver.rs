#![forbid(unsafe_code)]
// Only the driver is Rust: arrayStep/closureStep/natStep/natAccumulate
// are generated from the actual Lean compiler IR in the library.
use lean_generated::{arrayStep, closureStep, natAccumulate, natStep, __LeanValue};

fn array_checksum(iterations: usize) -> u64 {
    let mut state: u64 = 0x31415926D00DCAFE;
    let mut total: u64 = 0;
    for i in 0..iterations {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        total = total.wrapping_add(arrayStep(state, state.wrapping_add(i as u64)));
    }
    total
}

fn closure_checksum(iterations: usize) -> u64 {
    let mut state: u64 = 0x9E3779B97F4A7C15;
    let mut total: u64 = 0;
    for i in 0..iterations {
        state = state.wrapping_mul(2862933555777941757).wrapping_add(3037000493);
        total = total.wrapping_add(closureStep((i % 2 == 0) as u8, state, state.wrapping_add(7), state.wrapping_add(19)));
    }
    total
}

fn nat_checksum(iterations: usize) -> String {
    let a = [
        __LeanValue::nat_from_decimal("115792089237316195423570985008687907853269984665640564039457584007913129639953"),
        __LeanValue::nat_from_decimal("115792089237316195423570985008687907853269984665640564039457584007913129640015"),
    ];
    let b = [
        __LeanValue::nat_from_decimal("340282366920938463463374607431768211489"),
        __LeanValue::nat_from_decimal("340282366920938463463374607431768211517"),
    ];
    let mut total = __LeanValue::nat_from_decimal("0");
    for i in 0..iterations {
        let value = natStep(a[i % 2].clone(), b[usize::from(i % 3 != 0)].clone());
        total = natAccumulate(total, value);
    }
    total.nat_to_decimal()
}

fn main() {
    let mut args = std::env::args().skip(1);
    let kind = args.next().expect("expected benchmark type");
    let iterations: usize = args.next().expect("expected iteration count").parse().expect("count must be a Nat");
    assert!(args.next().is_none(), "unexpected arguments");
    match kind.as_str() {
        "array" => println!("{}", array_checksum(iterations)),
        "closure" => println!("{}", closure_checksum(iterations)),
        "nat" => println!("{}", nat_checksum(iterations)),
        _ => panic!("expected array, closure, or nat"),
    }
}
