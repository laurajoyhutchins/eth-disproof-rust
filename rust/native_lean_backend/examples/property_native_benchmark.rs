// Include exactly the emitted Lean IR implementation, not a Rust rewrite.
include!("generated_property.rs");

fn main() {
    let mut state: u64 = 0x9E3779B97F4A7C15;
    let mut result: u64 = 0;
    for i in 0_u64..1048576 {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        result = result.wrapping_add(property_hop(i % 17, state));
    }
    println!("{result}");
}
