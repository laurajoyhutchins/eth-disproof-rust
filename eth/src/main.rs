use lean_eth_reference::{EnumeratingLeaf, Limits, count_cnf, parse_dimacs};
use std::io::{self, Read};
fn main() {
    let mut source = String::new();
    if let Err(e) = io::stdin().read_to_string(&mut source) {
        eprintln!("input error: {e}");
        std::process::exit(2);
    }
    let result = parse_dimacs(&source).and_then(|cnf| {
        // Default is an **explicitly bounded exponential** semantic oracle.
        count_cnf(
            cnf.normalize(),
            2,
            &mut EnumeratingLeaf { max_variables: 20 },
            Limits::default(),
        )
    });
    match result {
        Ok((count, stats)) => println!(
            "count={count} nodes={} leaves={} peak_frontier={}",
            stats.nodes, stats.leaves, stats.peak_frontier
        ),
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(2);
        }
    }
}
