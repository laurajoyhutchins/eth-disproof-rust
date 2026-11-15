//! Source-CFG reference-count audit over borrowed Lean IR.
//! A nonrecursive join executes only when reached by an IR jump.
use super::*;

impl Reader {
    // An isShared expression is a physical ownership observation even when
    // the current generated value representation is immutable and Rc-backed.
    pub(super) unsafe fn shared_observations(body: Obj) -> CompilerResult<BTreeSet<usize>> {
        let mut observed = BTreeSet::new();
        let mut pending = vec![body];
        let mut count = 0usize;
        while let Some(current) = pending.pop() {
            count += 1;
            if count > 100_000 {
                return Err(CompilerError::new(RefusalKind::FnBody, "sharedness audit exceeds 100000 IR instructions"));
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

    // Follow executable source control flow rather than the syntax tree:
    // jdecl makes its binding visible but only jmp executes the value body.
    // Conservatively remember reference-count effects across all paths.
    // VarIds do not imply disjoint heap objects.
    pub(super) unsafe fn rc_may_precede_sharedness(body: Obj) -> CompilerResult<bool> {
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
                return Err(CompilerError::new(RefusalKind::FnBody, "source reference-count CFG audit limit exceeded"));
            }
            match Self::body_view(current)? {
                FnBodyView::Decl { expr, next, .. } => {
                    if prior_rc && Self::checked_tag(expr, "Expr")? == 12 {
                        return Ok(true);
                    }
                    pending.push((next, prior_rc, scope, depth));
                }
                FnBodyView::Join {
                    id, value, next, ..
                } => {
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
                FnBodyView::Inc { next, .. }
                | FnBodyView::Dec { next, .. }
                | FnBodyView::Delete { next, .. } => {
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
