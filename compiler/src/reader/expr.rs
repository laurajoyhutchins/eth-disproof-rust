//! Typed expression lowering from borrowed, source-checked Lean IR.
use super::*;

impl Reader {
    pub(super) unsafe fn expr(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
        ctx: LoweringContext<'_>,
        consumed_array: Option<usize>,
        consumed_calls: &BTreeSet<usize>,
        consumed_ap: Option<usize>,
    ) -> CompilerResult<String> {
        if is_value_type(var_ty) {
            RuntimeFeatures::mark(ctx.features, RuntimeFeatures::VALUE);
        }
        match Self::checked_tag(x, "Expr")? {
            0 => Self::lower_constructor(x, var_ty, env),
            3 => Self::lower_projection(x, var_ty, env),
            5 => Self::lower_scalar_projection(x, var_ty, env),
            7 => Self::lower_partial_application(x, var_ty, env, ctx.functions, ctx.features),
            8 => Self::lower_application(x, var_ty, env, consumed_ap),
            9 => Self::lower_box(x, var_ty, env),
            10 => Self::lower_unbox(x, var_ty, env),
            6 => Self::lower_full_application(
                x,
                var_ty,
                env,
                ctx.functions,
                consumed_array,
                consumed_calls,
                ctx.features,
            ),
            11 => Ok(Self::lit(Self::field(x, 0)?, var_ty)?),
            12 => Self::lower_shared_observation(x, var_ty, env),
            t => Err(CompilerError::new(
                RefusalKind::Expr,
                format!("IR expression constructor {t} unsupported"),
            )),
        }
    }
}
