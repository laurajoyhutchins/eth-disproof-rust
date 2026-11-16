//! Read-only, bounded observation of the same pinned Lean IR objects passed
//! to production Reader. Every field uses Reader's C-backed decode/view layer.
//!
//! This is *not* a second emitter: it produces a structural observation for
//! independent comparison with the original Lean.IR.Decl. No ownership
//! mutation or object retention occurs. It rejects unreviewed IR.

use super::*;

impl Reader {
    pub(crate) unsafe fn observe_scalar_ir(decl: Obj) -> CompilerResult<String> {
        if lr_abi_probe() == 0 {
            return Err(CompilerError::new(RefusalKind::Abi, "pinned Lean ABI probe failed"));
        }
        if Self::checked_tag(decl, "Decl")? != 0 {
            return Err(CompilerError::new(RefusalKind::Decl, "expected source IR fdecl"));
        }
        let name = Self::name(Self::field(decl, 0)?, 0)?;
        let params = Self::array(Self::field(decl, 1)?)?;
        if params.len() != 2 {
            return Err(CompilerError::new(RefusalKind::Decl, "scalar witness requires two arguments"));
        }
        if Self::ty(Self::field(decl, 2)?)? != "u64" {
            return Err(CompilerError::new(RefusalKind::Decl, "scalar witness requires UInt64 return"));
        }
        let mut out = format!("DECL {name}\n");
        let mut ids = BTreeSet::new();
        for p in params {
            let id = Self::var(Self::field(p, 0)?)?;
            let ty = Self::ty(Self::field(p, 1)?)?;
            if ty != "u64" || Self::param_borrow(p)? || !ids.insert(id) {
                return Err(CompilerError::new(
                    RefusalKind::Decl,
                    "scalar parameter must be a distinct unborrowed UInt64",
                ));
            }
            writeln!(&mut out, "PARAM {id} u64 0").unwrap();
        }
        out.push_str("RET u64\n");
        let mut budget = 0;
        Self::observe_scalar_body(Self::field(decl, 3)?, &mut out, 0, &mut budget)?;
        if out.len() > safety::MAX_OUTPUT_BYTES {
            return Err(CompilerError::new(
                RefusalKind::ResourceLimit,
                "scalar ABI readback exceeded source output limit",
            ));
        }
        Ok(out)
    }

    unsafe fn observe_scalar_arg(x: Obj) -> CompilerResult<usize> {
        if Self::checked_tag(x, "Arg")? != 0 {
            return Err(CompilerError::new(RefusalKind::Arg, "erased scalar ABI argument"));
        }
        Self::var(Self::field(x, 0)?)
    }

    unsafe fn observe_scalar_expr(x: Obj, out: &mut String) -> CompilerResult<()> {
        match Self::checked_tag(x, "Expr")? {
            11 => {
                let lit = Self::field(x, 0)?;
                if Self::checked_tag(lit, "LitVal")? != 0 {
                    return Err(CompilerError::new(RefusalKind::LitVal, "non-numeric literal"));
                }
                let n = Self::nat(Self::field(lit, 0)?)?;
                writeln!(out, "E L {n}").unwrap();
            }
            6 => {
                let name = Self::name(Self::field(x, 0)?, 0)?;
                if !matches!(
                    name.as_str(),
                    "UInt64.add" | "UInt64.mul" | "UInt64.decEq"
                        | "UInt64.decLt" | "UInt64.decLe"
                ) {
                    return Err(CompilerError::new(RefusalKind::Expr, "unproved source primitive"));
                }
                let args = Self::array(Self::field(x, 1)?)?;
                if args.len() != 2 {
                    return Err(CompilerError::new(RefusalKind::Expr, "scalar fap arity != 2"));
                }
                let a = Self::observe_scalar_arg(args[0])?;
                let b = Self::observe_scalar_arg(args[1])?;
                writeln!(out, "E F {name} {a} {b}").unwrap();
            }
            _ => return Err(CompilerError::new(RefusalKind::Expr, "unproved source IR expression")),
        }
        Ok(())
    }

    unsafe fn observe_scalar_body(
        x: Obj,
        out: &mut String,
        depth: usize,
        budget: &mut usize,
    ) -> CompilerResult<()> {
        if depth > 128 {
            return Err(CompilerError::new(
                RefusalKind::ResourceLimit,
                "scalar ABI readback nesting bound exceeded",
            ));
        }
        *budget += 1;
        if *budget > 100_000 {
            return Err(CompilerError::new(
                RefusalKind::ResourceLimit,
                "scalar ABI readback instruction bound exceeded",
            ));
        }
        match Self::body_view(x)? {
            FnBodyView::Decl {
                defined,
                ty,
                expr,
                next,
            } => {
                let id = Self::var(defined)?;
                let ty = Self::ty(ty)?;
                if !matches!(ty, "u64" | "u8") {
                    return Err(CompilerError::new(RefusalKind::IRType, "unproved binding type"));
                }
                writeln!(out, "V {id} {ty}").unwrap();
                Self::observe_scalar_expr(expr, out)?;
                Self::observe_scalar_body(next, out, depth + 1, budget)?;
            }
            FnBodyView::Return { value } => {
                let id = Self::observe_scalar_arg(value)?;
                writeln!(out, "RETURN {id}").unwrap();
            }
            FnBodyView::Case {
                scrutinee,
                alternatives,
            } => {
                let family = Self::name(Self::field(x, 0)?, 0)?;
                let ty = Self::ty(Self::field(x, 2)?)?;
                let id = Self::var(scrutinee)?;
                if family != "UInt8" || ty != "u8" {
                    return Err(CompilerError::new(RefusalKind::Alt, "unproved case representation"));
                }
                let alts = Self::array(alternatives)?;
                if alts.len() != 2 {
                    return Err(CompilerError::new(RefusalKind::Alt, "expected two Bool alternatives"));
                }
                writeln!(out, "CASE {family} {id} {ty} {}", alts.len()).unwrap();
                let mut seen = [false; 2];
                for alt in alts {
                    if Self::checked_tag(alt, "Alt")? != 0 {
                        return Err(CompilerError::new(RefusalKind::Alt, "unproved default alternative"));
                    }
                    let info = Self::field(alt, 0)?;
                    let name = Self::name(Self::field(info, 0)?, 0)?;
                    let tag = Self::nat(Self::field(info, 1)?)?;
                    if tag > 1 || seen[tag] ||
                        name != if tag == 0 { "Bool.false" } else { "Bool.true" } {
                        return Err(CompilerError::new(
                            RefusalKind::Alt,
                            "invalid, repeated or misnamed Bool constructor",
                        ));
                    }
                    seen[tag] = true;
                    writeln!(out, "ALT {name} {tag}").unwrap();
                    Self::observe_scalar_body(Self::field(alt, 1)?, out, depth + 1, budget)?;
                    out.push_str("ENDALT\n");
                }
                if !seen.into_iter().all(|v| v) {
                    return Err(CompilerError::new(RefusalKind::Alt, "incomplete Bool alternatives"));
                }
                out.push_str("ENDCASE\n");
            }
            _ => {
                return Err(CompilerError::new(
                    RefusalKind::FnBody,
                    "unproved original source IR body node",
                ))
            }
        }
        Ok(())
    }
}
