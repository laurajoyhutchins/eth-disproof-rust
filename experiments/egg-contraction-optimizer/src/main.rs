use egg_contraction_experiment::optimize;

fn main() {
    let examples = [
        ("cross-output association", "(pair (+ a (+ b c)) (+ (+ a b) d))"),
        ("factoring", "(pair (+ (* a b) (* a c)) (* a (+ b c)))"),
    ];
    for (label, expression) in examples {
        match optimize(expression, 100_000) {
            Ok(r) => {
                println!("{label}");
                println!("  unique arithmetic operations: {} -> {}", r.baseline.operation_count(), r.optimized.operation_count());
                println!("  DAG nodes: {} -> {}", r.baseline.node_count(), r.optimized.node_count());
                println!("  e-classes/e-nodes: {}/{}", r.eclasses, r.enodes);
                println!("  selection states: {}, complete: {}", r.search_states, r.complete);
                println!("  refused candidate improvements: {}", r.refused_candidates);
                println!("  saturation status: {}", r.saturation_stop);
                println!("  exploration + extraction time: {:?}", r.elapsed);
            }
            Err(e) => {
                eprintln!("{label}: refused: {e}");
                std::process::exit(1);
            }
        }
    }
}
