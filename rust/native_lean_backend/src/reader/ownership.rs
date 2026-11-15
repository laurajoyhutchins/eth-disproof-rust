//! Physical reference-count observation audit on source Lean IR CFG.
//! Nonrecursive join bindings are entered only by jump; no runtime RC claim.
use super::*;

impl Reader {
    // Gather all physical sharing observations in one declaration body.
    // IR variable identities are unique; unsupported shapes fail closed.
    pub(super) unsafe fn shared_observations(body: Obj) -> Result<BTreeSet<usize>, String> {
        let mut observed = BTreeSet::new();
        let mut pending = vec![body];
        let mut count = 0usize;
        while let Some(current) = pending.pop() {
            count += 1;
            if count > 100_000 {
                return Err("sharedness audit exceeds 100000 IR instructions".into());
            }
            match Self::checked_tag(current, "FnBody")? {
                0 => {
                    let expr = Self::field(current, 2)?;
                    if Self::checked_tag(expr, "Expr")? == 12 {
                        observed.insert(Self::var(Self::field(expr, 0)?)?);
                    }
                    pending.push(Self::field(current, 3)?);
                }
                1 => {
                    pending.push(Self::field(current, 2)?);
                    pending.push(Self::field(current, 3)?);
                }
                2 => pending.push(Self::field(current, 3)?),
                5 => pending.push(Self::field(current, 5)?),
                6 | 7 => pending.push(Self::field(current, 2)?),
                8 => pending.push(Self::field(current, 1)?),
                9 => {
                    for alt in Self::array(Self::field(current, 3)?)? {
                        let idx = match Self::checked_tag(alt, "Alt")? {
                            0 => 1,
                            1 => 0,
                            t => return Err(format!("unsupported sharedness audit Alt {t}")),
                        };
                        pending.push(Self::field(alt, idx)?);
                    }
                }
                10 | 11 => {}
                t => return Err(format!("unsupported sharedness audit FnBody {t}")),
            }
        }
        Ok(observed)
    }

    // Follow the actual Lean FnBody control-flow graph, not its syntax tree:
    // jdecl defines a join but does not execute its body until jmp.
    // Carry one conservative RC-effect bit along each executable path;
    // aliases are not assumed disjoint merely because VarIds differ.
    // Scope snapshots exclude a join from its own body, matching the
    // canonical emitter's nonrecursive join contract.
    pub(super) unsafe fn rc_may_precede_sharedness(body: Obj) -> Result<bool, String> {
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
            match Self::checked_tag(current, "FnBody")? {
                0 => {
                    let expr = Self::field(current, 2)?;
                    if prior_rc && Self::checked_tag(expr, "Expr")? == 12 {
                        return Ok(true);
                    }
                    pending.push((Self::field(current, 3)?, prior_rc, scope, depth));
                }
                1 => {
                    let id = Self::var(Self::field(current, 0)?)?;
                    let value = Self::field(current, 2)?;
                    let continuation = Self::field(current, 3)?;
                    let visible = Some(std::rc::Rc::new(JoinScope {
                        id,
                        body: value,
                        outer: scope,
                    }));
                    pending.push((continuation, prior_rc, visible, depth + 1));
                }
                2 => pending.push((Self::field(current, 3)?, prior_rc, scope, depth)),
                5 => pending.push((Self::field(current, 5)?, prior_rc, scope, depth)),
                6 | 7 => pending.push((Self::field(current, 2)?, true, scope, depth)),
                8 => pending.push((Self::field(current, 1)?, true, scope, depth)),
                9 => {
                    for alt in Self::array(Self::field(current, 3)?)? {
                        let idx = match Self::checked_tag(alt, "Alt")? {
                            0 => 1,
                            1 => 0,
                            t => return Err(format!("unsupported RC CFG alternative {t}")),
                        };
                        pending.push((Self::field(alt, idx)?, prior_rc, scope.clone(), depth + 1));
                    }
                }
                10 => {}
                11 => {
                    let id = Self::var(Self::field(current, 0)?)?;
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
                t => return Err(format!("unsupported RC CFG FnBody constructor {t}")),
            }
        }
        Ok(false)
    }

}
