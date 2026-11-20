//! Source-derived order for the bounded straight-line ownership fragment.
//!
//! This reads the *actual borrowed Lean compiler IR*, not a handwritten
//! transcript. Branches, joins, calls, and non-literal expressions have no
//! claim in this checker. Distinct IR variables are not presumed nonaliasing.
use super::*;
use super::effect_order::Event;

impl Reader {
    pub(super) unsafe fn linear_source_effects(
        mut body: Obj,
    ) -> CompilerResult<Option<Vec<Event>>> {
        let mut events = Vec::new();
        for _ in 0..100_000 {
            let current = body;
            match Self::body_view(current)? {
                FnBodyView::Decl {
                    defined, expr, next, ..
                } => {
                    match Self::checked_tag(expr, "Expr")? {
                        11 => {} // Pure compiler literal; no source effect.
                        12 => events.push(Event::Observe {
                            result: Self::var(defined)?,
                            var: Self::var(Self::field(expr, 0)?)?,
                        }),
                        _ => return Ok(None), // No claim for unknown effects.
                    }
                    body = next;
                }
                FnBodyView::Inc {
                    target,
                    checked,
                    persistent,
                    next,
                } => {
                    events.push(Event::Inc {
                        var: Self::var(target)?,
                        count: Self::nat(Self::field(current, 1)?)?,
                        checked,
                        persistent,
                    });
                    body = next;
                }
                FnBodyView::Dec {
                    target,
                    checked,
                    persistent,
                    next,
                } => {
                    events.push(Event::Dec {
                        var: Self::var(target)?,
                        count: Self::nat(Self::field(current, 1)?)?,
                        checked,
                        persistent,
                    });
                    body = next;
                }
                FnBodyView::Delete { target, next } => {
                    events.push(Event::Delete {
                        var: Self::var(target)?,
                    });
                    body = next;
                }
                FnBodyView::Return { .. } => return Ok(Some(events)),
                // Control-flow and mutation semantics are not linear receipts.
                FnBodyView::Join { .. }
                | FnBodyView::Case { .. }
                | FnBodyView::Jump { .. }
                | FnBodyView::Set { .. }
                | FnBodyView::ScalarSet { .. } => return Ok(None),
            }
        }
        Err(CompilerError::new(
            RefusalKind::ResourceLimit,
            "linear source ownership receipt exceeds 100000 nodes",
        ))
    }
}
