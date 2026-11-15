//! Source-ordered physical ownership admission over borrowed Lean compiler IR.
//! The emitted Rc representation is not the source physical reference-count
//! machine. We therefore reject observations after potentially unmatched RC
//! effects, including effects through direct calls, joins, cases and closures.
use super::*;

// Interprocedural summaries are a conservative may-analysis. Syntactic
// closure creation does *not* execute its callee; actual indirect AP does.
#[derive(Default)]
pub(super) struct OwnershipSummary {
    may_effect: BTreeSet<String>,
    may_observe: BTreeSet<String>,
    known_functions: BTreeSet<String>,
}

#[derive(Default)]
struct LocalEffects {
    effect: bool,
    observe: bool,
    direct_calls: BTreeSet<String>,
    partial_calls: BTreeSet<String>,
}

impl Reader {
    pub(super) unsafe fn shared_observations(body: Obj) -> CompilerResult<BTreeSet<usize>> {
        let mut observed = BTreeSet::new();
        let mut pending = vec![body];
        let mut count = 0usize;
        while let Some(current) = pending.pop() {
            count += 1;
            if count > 100_000 {
                return Err("sharedness audit exceeds 100000 IR instructions".into());
            }
            match Self::body_view(current)? {
                FnBodyView::Decl { expr, next, .. } => {
                    if Self::checked_tag(expr, "Expr")? == 12 {
                        observed.insert(Self::var(Self::field(expr, 0)?)?);
                    }
                    pending.push(next);
                }
                FnBodyView::Join { value, next, .. } => {
                    pending.push(value);
                    pending.push(next);
                }
                FnBodyView::Case { alternatives, .. } => {
                    for alt in Self::array(alternatives)? {
                        let branch = match Self::alt_view(alt)? {
                            AltView::Constructor { body } | AltView::Default { body } => body,
                        };
                        pending.push(branch);
                    }
                }
                FnBodyView::Set { next, .. }
                | FnBodyView::ScalarSet { next, .. }
                | FnBodyView::Inc { next, .. }
                | FnBodyView::Dec { next, .. }
                | FnBodyView::Delete { next, .. } => pending.push(next),
                FnBodyView::Return { .. } | FnBodyView::Jump { .. } => {}
            }
        }
        Ok(observed)
    }

    // Analyze every source alternative and lexically defined join body.
    // This over-approximates executable effects without pretending that a
    // declared, unentered join or PAP eagerly calls its target.
    unsafe fn local_effects(body: Obj) -> CompilerResult<LocalEffects> {
        let mut result = LocalEffects::default();
        let mut pending = vec![body];
        let mut count = 0usize;
        while let Some(current) = pending.pop() {
            count += 1;
            if count > 100_000 {
                return Err("source ownership effect scan limit exceeded".into());
            }
            match Self::body_view(current)? {
                FnBodyView::Decl { expr, next, .. } => {
                    match Self::checked_tag(expr, "Expr")? {
                        1 | 2 | 8 => result.effect = true, // reset, reuse, indirect AP
                        6 => {
                            result.direct_calls.insert(Self::name(Self::field(expr, 0)?, 0)?);
                        }
                        7 => {
                            result.partial_calls.insert(Self::name(Self::field(expr, 0)?, 0)?);
                        }
                        12 => result.observe = true,
                        _ => {}
                    }
                    pending.push(next);
                }
                FnBodyView::Join { value, next, .. } => {
                    pending.push(value);
                    pending.push(next);
                }
                FnBodyView::Case { alternatives, .. } => {
                    for alt in Self::array(alternatives)? {
                        let branch = match Self::alt_view(alt)? {
                            AltView::Constructor { body } | AltView::Default { body } => body,
                        };
                        pending.push(branch);
                    }
                }
                FnBodyView::Inc { persistent, next, .. }
                | FnBodyView::Dec { persistent, next, .. } => {
                    result.effect |= !persistent;
                    pending.push(next);
                }
                FnBodyView::Delete { next, .. } => {
                    result.effect = true;
                    pending.push(next);
                }
                FnBodyView::Set { next, .. } | FnBodyView::ScalarSet { next, .. } => {
                    pending.push(next);
                }
                FnBodyView::Return { .. } | FnBodyView::Jump { .. } => {}
            }
        }
        Ok(result)
    }

    // Fixed point over the exact, requested-root executable declaration
    // closure, including recursive direct-call cycles. Missing primitive
    // bodies conservatively count as potential effects.
    pub(super) unsafe fn ownership_summary(
        closure: &BTreeMap<String, Obj>,
    ) -> CompilerResult<OwnershipSummary> {
        let mut locals = BTreeMap::<String, LocalEffects>::new();
        let mut summary = OwnershipSummary::default();
        summary.known_functions.extend(closure.keys().cloned());
        for (name, decl) in closure {
            let effects = Self::local_effects(Self::field(*decl, 3)?)?;
            if effects.effect || effects.direct_calls.iter().any(|c| !closure.contains_key(c)) {
                summary.may_effect.insert(name.clone());
            }
            if effects.observe {
                summary.may_observe.insert(name.clone());
            }
            locals.insert(name.clone(), effects);
        }
        // Every successful iteration adds at least one of at most 2*n facts.
        for _ in 0..(2 * closure.len() + 1) {
            let mut changed = false;
            for (name, effects) in &locals {
                if effects.direct_calls.iter().any(|callee| summary.may_effect.contains(callee)) {
                    changed |= summary.may_effect.insert(name.clone());
                }
                if effects.direct_calls.iter().any(|callee| summary.may_observe.contains(callee)) {
                    changed |= summary.may_observe.insert(name.clone());
                }
            }
            if !changed {
                return Ok(summary);
            }
        }
        Err("ownership call-effect fixed point did not converge".into())
    }

    // Source PAPs transfer captured references into a closure object. If the
    // target observes physical sharing, the immutable Rc closure adapter has
    // no proven capture/borrow correspondence, even if its body has no RC ops.
    pub(super) unsafe fn captures_observer(
        body: Obj,
        summary: &OwnershipSummary,
    ) -> CompilerResult<bool> {
        let events = Self::local_effects(body)?;
        Ok(events.partial_calls.iter().any(|c| summary.may_observe.contains(c)))
    }

    // Actual executable path analysis; join bodies are visited only at a
    // jump, and branch histories never leak into sibling alternatives.
    // At an observation or call into an observing callee, any earlier
    // possible effect is a hard refusal. Unknown indirect applications
    // taint subsequent observations.
    pub(super) unsafe fn rc_may_precede_sharedness(
        body: Obj,
        summary: Option<&OwnershipSummary>,
    ) -> CompilerResult<bool> {
        #[derive(Clone)]
        struct JoinScope {
            id: usize,
            body: Obj,
            outer: Option<std::rc::Rc<JoinScope>>,
        }
        let mut pending = vec![(body, false, None::<std::rc::Rc<JoinScope>>, 0usize)];
        let mut steps = 0usize;
        while let Some((current, prior_rc, scope, depth)) = pending.pop() {
            steps += 1;
            if steps > 100_000 || depth > 128 {
                return Err("source reference-count CFG audit limit exceeded".into());
            }
            match Self::body_view(current)? {
                FnBodyView::Decl { expr, next, .. } => {
                    let tag = Self::checked_tag(expr, "Expr")?;
                    if prior_rc && tag == 12 {
                        return Ok(true);
                    }
                    let mut effects = prior_rc;
                    match tag {
                        1 | 2 | 8 => effects = true, // reset, reuse, unknown AP
                        6 => {
                            let name = Self::name(Self::field(expr, 0)?, 0)?;
                            if let Some(s) = summary {
                                if prior_rc && s.may_observe.contains(&name) {
                                    return Ok(true);
                                }
                                // If a primitive call is absent from the
                                // source closure, it has unknown RC effects.
                                effects |= !s.known_functions.contains(&name)
                                    || s.may_effect.contains(&name);
                            }
                        }
                        _ => {}
                    }
                    pending.push((next, effects, scope, depth));
                }
                FnBodyView::Join { id, value, next, .. } => {
                    let id = Self::var(id)?;
                    let visible = Some(std::rc::Rc::new(JoinScope {
                        id,
                        body: value,
                        outer: scope,
                    }));
                    pending.push((next, prior_rc, visible, depth + 1));
                }
                FnBodyView::Set { next, .. } | FnBodyView::ScalarSet { next, .. } => {
                    pending.push((next, prior_rc, scope, depth));
                }
                FnBodyView::Inc { persistent, next, .. }
                | FnBodyView::Dec { persistent, next, .. } => {
                    pending.push((next, prior_rc || !persistent, scope, depth));
                }
                FnBodyView::Delete { next, .. } => {
                    pending.push((next, true, scope, depth));
                }
                FnBodyView::Case { alternatives, .. } => {
                    for alt in Self::array(alternatives)? {
                        let branch = match Self::alt_view(alt)? {
                            AltView::Constructor { body } | AltView::Default { body } => body,
                        };
                        pending.push((branch, prior_rc, scope.clone(), depth + 1));
                    }
                }
                FnBodyView::Return { .. } => {}
                FnBodyView::Jump { id, .. } => {
                    let id = Self::var(id)?;
                    let mut candidate = scope.as_ref();
                    let mut target = None;
                    while let Some(join) = candidate {
                        if join.id == id {
                            target = Some((join.body, join.outer.clone()));
                            break;
                        }
                        candidate = join.outer.as_ref();
                    }
                    let (body, outer) = target.ok_or_else(|| {
                        format!("unsupported or recursive RC CFG jump to join {id}")
                    })?;
                    pending.push((body, prior_rc, outer, depth + 1));
                }
            }
        }
        Ok(false)
    }
}
