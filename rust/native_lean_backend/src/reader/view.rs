//! A borrowed, checked view of the pinned Lean 4.34.1 control-flow IR.
//!
//! This is not an independent IR: each field remains a borrowed Lean object
//! read through the existing version-pinned ABI, without retaining pointers,
//! cloning Lean objects or guessing constructor layouts.
use super::*;

pub(super) enum FnBodyView {
    Decl {
        defined: Obj,
        ty: Obj,
        expr: Obj,
        next: Obj,
    },
    Join {
        id: Obj,
        params: Obj,
        value: Obj,
        next: Obj,
    },
    Set {
        target: Obj,
        index: Obj,
        value: Obj,
        next: Obj,
    },
    ScalarSet {
        target: Obj,
        pointers: Obj,
        offset: Obj,
        value: Obj,
        ty: Obj,
        next: Obj,
    },
    Inc {
        target: Obj,
        persistent: bool,
        next: Obj,
    },
    Dec {
        target: Obj,
        persistent: bool,
        next: Obj,
    },
    Delete {
        target: Obj,
        next: Obj,
    },
    Case {
        scrutinee: Obj,
        alternatives: Obj,
    },
    Return {
        value: Obj,
    },
    Jump {
        id: Obj,
        arguments: Obj,
    },
}

pub(super) enum AltView {
    Constructor { body: Obj },
    Default { body: Obj },
}

impl Reader {
    unsafe fn rc_persistent(x: Obj) -> CompilerResult<bool> {
        match lr_ir_rc_flags(x) {
            0 | 1 => Ok(false),
            2 | 3 => Ok(true),
            _ => Err("invalid pinned Lean.IR inc/dec packed Bool flags".into()),
        }
    }

    pub(super) unsafe fn body_view(x: Obj) -> CompilerResult<FnBodyView> {
        Ok(match Self::checked_tag(x, "FnBody")? {
            0 => FnBodyView::Decl {
                defined: Self::field(x, 0)?,
                ty: Self::field(x, 1)?,
                expr: Self::field(x, 2)?,
                next: Self::field(x, 3)?,
            },
            1 => FnBodyView::Join {
                id: Self::field(x, 0)?,
                params: Self::field(x, 1)?,
                value: Self::field(x, 2)?,
                next: Self::field(x, 3)?,
            },
            2 => FnBodyView::Set {
                target: Self::field(x, 0)?,
                index: Self::field(x, 1)?,
                value: Self::field(x, 2)?,
                next: Self::field(x, 3)?,
            },
            5 => FnBodyView::ScalarSet {
                target: Self::field(x, 0)?,
                pointers: Self::field(x, 1)?,
                offset: Self::field(x, 2)?,
                value: Self::field(x, 3)?,
                ty: Self::field(x, 4)?,
                next: Self::field(x, 5)?,
            },
            6 => FnBodyView::Inc {
                target: Self::field(x, 0)?,
                persistent: Self::rc_persistent(x)?,
                next: Self::field(x, 2)?,
            },
            7 => FnBodyView::Dec {
                target: Self::field(x, 0)?,
                persistent: Self::rc_persistent(x)?,
                next: Self::field(x, 2)?,
            },
            8 => FnBodyView::Delete {
                target: Self::field(x, 0)?,
                next: Self::field(x, 1)?,
            },
            9 => FnBodyView::Case {
                scrutinee: Self::field(x, 1)?,
                alternatives: Self::field(x, 3)?,
            },
            10 => FnBodyView::Return {
                value: Self::field(x, 0)?,
            },
            11 => FnBodyView::Jump {
                id: Self::field(x, 0)?,
                arguments: Self::field(x, 1)?,
            },
            t => {
                return Err(CompilerError::new(
                    RefusalKind::FnBody,
                    format!("IR body constructor {t} unsupported"),
                ))
            }
        })
    }

    pub(super) unsafe fn alt_view(x: Obj) -> CompilerResult<AltView> {
        Ok(match Self::checked_tag(x, "Alt")? {
            0 => AltView::Constructor {
                body: Self::field(x, 1)?,
            },
            1 => AltView::Default {
                body: Self::field(x, 0)?,
            },
            t => {
                return Err(CompilerError::new(
                    RefusalKind::Alt,
                    format!("IR alternative constructor {t} unsupported"),
                ))
            }
        })
    }
}
