fn main() -> lungo_build::Result<()> {
    // Only facade probes are exported. The imported compiler definitions
    // and executable dependency closure come from original Lean.
    lungo_build::configure()
        .export("Bootstrap.probe_scalar")
        .export("Bootstrap.probe_object")
        .export("Bootstrap.probe_possible_ref")
        .export("Bootstrap.probe_definite_ref")
        .export("Bootstrap.probe_erased")
        .export("Bootstrap.probe_boxed_tagged")
        .require_claims("Bootstrap.probe_scalar")
        .compile_lean("lean")
}
