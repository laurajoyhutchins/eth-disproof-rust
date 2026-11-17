fn main() -> lungo_build::Result<()> {
    // A narrow facade around the original Lean compiler configuration type.
    lungo_build::configure()
        .export("CompilerConfig.probe_eta")
        .export("CompilerConfig.probe_inline_partial")
        .export("CompilerConfig.probe_implemented_by")
        .export("CompilerConfig.probe_inline_defs")
        .require_claims("CompilerConfig.probe_eta")
        .compile_lean("lean")
}
