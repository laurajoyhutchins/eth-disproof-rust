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
    if let Err(error) = sat_fixture() {
        eprintln!("SAT boundary fixture refused: {error}");
        std::process::exit(1);
    }
}

fn sat_fixture() -> Result<(), String> {
    use egg_contraction_experiment::sat::{
        optimize_and_verify, three_branch_region, Association,
    };

    let first = three_branch_region("d");
    let second = three_branch_region("e");
    let report = optimize_and_verify(
        [&first, &second],
        [Association::Right, Association::Left],
        4, 16, 100_000,
    )?;
    println!("SAT-derived two-region boundary contraction:");
    println!("  source expression: {}", report.source_expression);
    println!(
        "  unique DAG arithmetic operations: {} -> {}",
        report.optimization.baseline.operation_count(),
        report.optimization.optimized.operation_count(),
    );
    println!(
        "  all {} boundary contexts checked against independent CNF enumeration",
        report.boundary.boundary_assignments_checked,
    );
    println!(
        "  direct internal states per boundary context: {}",
        report.boundary.internal_assignments_per_context,
    );
    println!(
        "  full boundary-table arithmetic operations: {} -> {}",
        report.boundary.baseline_arithmetic_evaluations,
        report.boundary.optimized_arithmetic_evaluations,
    );
    println!(
        "  operand-byte proxy (not bit operations): {} -> {}",
        report.boundary.baseline_operand_byte_proxy,
        report.boundary.optimized_operand_byte_proxy,
    );
    println!("  finite extraction complete: {}", report.optimization.complete);
    println!("  saturation status: {}", report.optimization.saturation_stop);
    println!("  signed outer-context checks: {}", report.boundary.weighted_outer_context_checked);
    Ok(())
}
