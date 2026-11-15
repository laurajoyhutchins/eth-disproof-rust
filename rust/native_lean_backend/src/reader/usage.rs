//! Conservative IR use and last-use analysis for owned value transfers.
use super::*;

impl Reader {
    // Last-use analysis only permits moves through a straight-line tail.
    // Any join, branch, unknown expression, or reference bookkeeping for the
    // candidate is conservatively considered an additional use. This avoids
    // unnecessary transient Rc aliases, but does not prove Lean's physical
    // reference-count trace equals Rust's trace.
    pub(super) unsafe fn arg_refs(x: Obj, id: usize) -> Result<bool, String> {
        Ok(match Self::checked_tag(x, "Arg")? {
            0 => Self::var(Self::field(x, 0)?)? == id,
            1 => false,
            _ => true,
        })
    }

    pub(super) unsafe fn args_ref(args: Obj, id: usize) -> Result<bool, String> {
        for arg in Self::array(args)? {
            if Self::arg_refs(arg, id)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) unsafe fn expr_refs(x: Obj, id: usize) -> Result<bool, String> {
        Ok(match Self::checked_tag(x, "Expr")? {
            0 => Self::args_ref(Self::field(x, 1)?, id)?,
            3 | 9 => Self::var(Self::field(x, 1)?)? == id,
            6 | 7 => Self::args_ref(Self::field(x, 1)?, id)?,
            8 => Self::var(Self::field(x, 0)?)? == id || Self::args_ref(Self::field(x, 1)?, id)?,
            10 => Self::var(Self::field(x, 0)?)? == id,
            11 => false,
            _ => true,
        })
    }

    pub(super) unsafe fn straight_tail_unused(mut x: Obj, id: usize) -> Result<bool, String> {
        for _ in 0..100_000 {
            match Self::body_view(x)? {
                FnBodyView::Decl { expr, next, .. } => {
                    if Self::expr_refs(expr, id)? {
                        return Ok(false);
                    }
                    x = next;
                }
                FnBodyView::Inc { target, next } | FnBodyView::Dec { target, next } => {
                    if Self::var(target)? == id {
                        return Ok(false);
                    }
                    x = next;
                }
                FnBodyView::Delete { target, next } => {
                    if Self::var(target)? == id {
                        return Ok(false);
                    }
                    x = next;
                }
                FnBodyView::Return { value } => return Ok(!Self::arg_refs(value, id)?),
                // Joins, branches and other effects forbid this fast path.
                _ => return Ok(false),
            }
        }
        Ok(false)
    }

    pub(super) unsafe fn tail_unused_on_all_paths(body: Obj, id: usize) -> Result<bool, String> {
        let mut pending = vec![(body, 0usize)];
        let mut steps = 0usize;
        while let Some((current, depth)) = pending.pop() {
            steps += 1;
            if steps > 100_000 || depth > 128 {
                return Ok(false);
            }
            let next_depth = depth + 1;
            match Self::body_view(current)? {
                FnBodyView::Decl {
                    defined,
                    expr,
                    next,
                    ..
                } => {
                    if Self::var(defined)? == id || Self::expr_refs(expr, id)? {
                        return Ok(false);
                    }
                    pending.push((next, depth));
                }
                FnBodyView::Join {
                    params,
                    value,
                    next,
                    ..
                } => {
                    // A lexical join may capture the candidate even when its
                    // continuation makes no explicit use of the variable.
                    for param in Self::array(params)? {
                        if Self::var(Self::field(param, 0)?)? == id {
                            return Ok(false);
                        }
                    }
                    pending.push((value, next_depth));
                    pending.push((next, depth));
                }
                FnBodyView::Set {
                    target,
                    value,
                    next,
                    ..
                } => {
                    if Self::var(target)? == id || Self::arg_refs(value, id)? {
                        return Ok(false);
                    }
                    pending.push((next, depth));
                }
                FnBodyView::ScalarSet {
                    target,
                    value,
                    next,
                    ..
                } => {
                    if Self::var(target)? == id || Self::var(value)? == id {
                        return Ok(false);
                    }
                    pending.push((next, depth));
                }
                FnBodyView::Inc { target, next } | FnBodyView::Dec { target, next } => {
                    if Self::var(target)? == id {
                        return Ok(false);
                    }
                    pending.push((next, depth));
                }
                FnBodyView::Delete { target, next } => {
                    if Self::var(target)? == id {
                        return Ok(false);
                    }
                    pending.push((next, depth));
                }
                FnBodyView::Case {
                    scrutinee,
                    alternatives,
                } => {
                    if Self::var(scrutinee)? == id {
                        return Ok(false);
                    }
                    for alt in Self::array(alternatives)? {
                        let branch = match Self::alt_view(alt)? {
                            AltView::Constructor { body } | AltView::Default { body } => body,
                        };
                        pending.push((branch, next_depth));
                    }
                }
                FnBodyView::Return { value } => {
                    if Self::arg_refs(value, id)? {
                        return Ok(false);
                    }
                }
                FnBodyView::Jump { arguments, .. } => {
                    if Self::args_ref(arguments, id)? {
                        return Ok(false);
                    }
                }
            }
        }
        Ok(true)
    }

    pub(super) unsafe fn consumable_array(expr: Obj, tail: Obj) -> Result<Option<usize>, String> {
        if Self::checked_tag(expr, "Expr")? != 6 {
            return Ok(None);
        }
        let name = Self::name(Self::field(expr, 0)?, 0)?;
        let arity = match name.as_str() {
            "Array.push" => 3,
            "Array.set!" => 4,
            _ => return Ok(None),
        };
        let args = Self::array(Self::field(expr, 1)?)?;
        if args.len() != arity || Self::checked_tag(args[1], "Arg")? != 0 {
            return Ok(None);
        }
        let id = Self::var(Self::field(args[1], 0)?)?;
        for arg in args.iter().skip(2) {
            if Self::arg_refs(*arg, id)? {
                return Ok(None);
            }
        }
        Ok(Self::tail_unused_on_all_paths(tail, id)?.then_some(id))
    }

    // An indirect AP can consume its closure only at its proven last IR
    // use. All branches and lexical joins are scanned; unknown constructs
    // refuse the optimization. Arguments may not alias the function itself.
    pub(super) unsafe fn consumable_ap(expr: Obj, tail: Obj) -> Result<Option<usize>, String> {
        if Self::checked_tag(expr, "Expr")? != 8 {
            return Ok(None);
        }
        let id = Self::var(Self::field(expr, 0)?)?;
        for arg in Self::array(Self::field(expr, 1)?)? {
            if Self::arg_refs(arg, id)? {
                return Ok(None);
            }
        }
        Ok(Self::tail_unused_on_all_paths(tail, id)?.then_some(id))
    }

    // A direct callee takes ownership of its argument. Moving an object at
    // its unique final use avoids manufacturing a temporary Rust Rc alias.
    // Do not extend this analysis through joins, branches, indirect calls,
    // bookkeeping, or unrecognized expressions.
    pub(super) unsafe fn consumable_call(
        expr: Obj,
        tail: Obj,
        functions: Option<&FunctionTable>,
    ) -> Result<BTreeSet<usize>, String> {
        let mut consumed = BTreeSet::new();
        if Self::checked_tag(expr, "Expr")? != 6 {
            return Ok(consumed);
        }
        let name = Self::name(Self::field(expr, 0)?, 0)?;
        let Some(signature) = functions.and_then(|f| f.get(&name)) else {
            return Ok(consumed);
        };
        let args = Self::array(Self::field(expr, 1)?)?;
        if args.len() != signature.params.len() {
            return Ok(consumed);
        }
        let mut counts = BTreeMap::<usize, usize>::new();
        for arg in &args {
            if Self::checked_tag(*arg, "Arg")? == 0 {
                let id = Self::var(Self::field(*arg, 0)?)?;
                *counts.entry(id).or_default() += 1;
            }
        }
        for (arg, ty) in args.into_iter().zip(signature.params.iter()) {
            if !is_value_type(ty) || Self::checked_tag(arg, "Arg")? != 0 {
                continue;
            }
            let id = Self::var(Self::field(arg, 0)?)?;
            if counts.get(&id) == Some(&1) && Self::straight_tail_unused(tail, id)? {
                consumed.insert(id);
            }
        }
        Ok(consumed)
    }
}
