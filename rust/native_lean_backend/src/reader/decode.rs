//! Source-checked reads of borrowed Lean 4.34.1 IR objects.
use super::*;

impl Reader {
    pub(super) unsafe fn scalar(x: Obj) -> CompilerResult<usize> {
        if lr_is_scalar(x) == 0 {
            Err(CompilerError::new(
                RefusalKind::Abi,
                "expected tagged scalar",
            ))
        } else {
            Ok(lr_scalar_value(x))
        }
    }
    pub(super) unsafe fn tag(x: Obj) -> CompilerResult<usize> {
        if lr_is_scalar(x) != 0 {
            return Ok(lr_scalar_value(x));
        }
        if lr_is_ctor(x) == 0 {
            return Err(CompilerError::new(
                RefusalKind::Abi,
                "expected inductive constructor",
            ));
        }
        Ok(lr_tag(x) as usize)
    }
    pub(super) unsafe fn checked_tag(x: Obj, family: &str) -> CompilerResult<usize> {
        let tag = Self::tag(x)?;
        if SUPPORTED_IR_TAGS.contains(&(family, tag)) {
            Ok(tag)
        } else {
            Err(CompilerError::new(
                RefusalKind::ir_family(family),
                format!(
                    "{family} constructor tag {tag} explicitly unsupported by pinned IR coverage contract"
                ),
            ))
        }
    }
    pub(super) unsafe fn field(x: Obj, index: usize) -> CompilerResult<Obj> {
        if lr_is_ctor(x) == 0 || index >= lr_field_count(x) {
            return Err(CompilerError::new(
                RefusalKind::Abi,
                format!(
                    "constructor field {index} unavailable (tag={}, fields={}, scalar={})",
                    lr_tag(x),
                    lr_field_count(x),
                    lr_is_scalar(x)
                ),
            ));
        }
        Ok(lr_field(x, index))
    }
    pub(super) unsafe fn array(x: Obj) -> CompilerResult<Vec<Obj>> {
        if lr_is_array(x) == 0 {
            return Err(CompilerError::new(RefusalKind::Abi, "expected Lean Array"));
        }
        let count = lr_array_len(x);
        if count > 1_000_000 {
            return Err(CompilerError::new(
                RefusalKind::ResourceLimit,
                "IR node array exceeds safety cap",
            ));
        }
        Ok((0..count).map(|i| lr_array_at(x, i)).collect())
    }
    pub(crate) unsafe fn string(x: Obj) -> CompilerResult<String> {
        let ptr = lr_string_ptr(x);
        if ptr.is_null() {
            return Err(CompilerError::new(RefusalKind::Abi, "expected Lean String"));
        }
        let len = lr_string_size(x);
        if len == 0 || len > 1_048_577 {
            return Err(CompilerError::new(
                RefusalKind::Abi,
                "Lean String byte length outside supported bound",
            ));
        }
        let bytes = std::slice::from_raw_parts(ptr.cast::<u8>(), len - 1);
        String::from_utf8(bytes.to_vec())
            .map_err(|_| CompilerError::new(RefusalKind::Abi, "invalid UTF-8"))
    }
    // Convert an arbitrary-precision source Nat through Lean's pinned public
    // runtime API, never by interpreting GMP limbs or truncating to usize.
    pub(super) unsafe fn decimal_nat(x: Obj) -> CompilerResult<String> {
        let raw = lr_nat_decimal(x);
        if raw.is_null() {
            return Err(CompilerError::new(
                RefusalKind::ResourceLimit,
                "large Nat literal rejected (invalid or over 4 KiB)",
            ));
        }
        let decoded = CStr::from_ptr(raw)
            .to_str()
            .map(str::to_owned)
            .map_err(|_| {
                CompilerError::new(
                    RefusalKind::LitVal,
                    "invalid Nat literal decimal representation",
                )
            });
        lr_free_string(raw);
        decoded
    }
    pub(super) unsafe fn nat(x: Obj) -> CompilerResult<usize> {
        Self::scalar(x).map_err(|_| {
            CompilerError::new(RefusalKind::Abi, "large Nat unsupported by v0 compiler")
        })
    }
    // Name paths retain an injective identity, not a lossy pretty-print.
    // Plain ASCII segments keep historical spelling for pinned primitives;
    // special UTF-8 strings use ~s<hex bytes>, numeric segments use ~n<nat>.
    pub(super) unsafe fn name(x: Obj, depth: usize) -> CompilerResult<String> {
        if depth > 128 {
            return Err(CompilerError::new(
                RefusalKind::ResourceLimit,
                "name nesting limit",
            ));
        }
        match Self::tag(x)? {
            0 => Ok(String::new()),
            1 => {
                let parent = Self::name(Self::field(x, 0)?, depth + 1)?;
                let component = Self::string(Self::field(x, 1)?)?;
                let encoded = encode_name_str(&component)
                    .map_err(|error| CompilerError::new(RefusalKind::Decl, error))?;
                Ok(append_name_component(&parent, &encoded))
            }
            2 => {
                let parent = Self::name(Self::field(x, 0)?, depth + 1)?;
                let number = Self::nat(Self::field(x, 1)?)?;
                Ok(append_name_component(&parent, &format!("~n{number}")))
            }
            t => Err(CompilerError::new(
                RefusalKind::Decl,
                format!("unknown Lean.Name tag {t}"),
            )),
        }
    }
    // Param.borrow is an unboxed Bool in pinned Lean IR.Param, not one of
    // its two pointer fields. The Lean C ABI verifies its actual layout.
    pub(super) unsafe fn param_borrow(x: Obj) -> CompilerResult<bool> {
        match lr_param_borrow(x) {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(CompilerError::new(
                RefusalKind::Abi,
                "unsupported Lean IR.Param borrowed-flag layout",
            )),
        }
    }

    pub(super) unsafe fn var(x: Obj) -> CompilerResult<usize> {
        // A Lean single-field structure may be represented as its single field
        // after erasure; accept both representations, reject all other cases.
        if lr_is_scalar(x) != 0 {
            return Self::nat(x);
        }
        if lr_is_ctor(x) != 0 && lr_field_count(x) == 1 {
            return Self::nat(Self::field(x, 0)?);
        }
        Err(CompilerError::new(
            RefusalKind::Abi,
            "unsupported VarId runtime representation",
        ))
    }
    pub(super) unsafe fn arg(
        x: Obj,
        env: &BTreeMap<usize, &'static str>,
        expected: &str,
    ) -> CompilerResult<String> {
        match Self::checked_tag(x, "Arg")? {
            0 => {
                let id = Self::var(Self::field(x, 0)?)?;
                let found = env.get(&id).ok_or_else(|| {
                    CompilerError::new(RefusalKind::Arg, format!("unknown input variable x_{id}"))
                })?;
                if !ir_type_compatible(found, expected) {
                    return Err(CompilerError::new(
                        RefusalKind::Arg,
                        format!("x_{id}: expected {expected}, got {found}"),
                    ));
                }
                Ok(if is_value_type(found) {
                    format!("x_{id}.clone()")
                } else {
                    format!("x_{id}")
                })
            }
            1 => Err(CompilerError::new(
                RefusalKind::Arg,
                "erased value used as runtime operand",
            )),
            t => Err(CompilerError::new(
                RefusalKind::Arg,
                format!("unknown Arg constructor {t}"),
            )),
        }
    }
    pub(super) unsafe fn ty(x: Obj) -> CompilerResult<&'static str> {
        // The tag ordering comes from the pinned Lean.Compiler.IR.Basic.
        match Self::checked_tag(x, "IRType")? {
            0 => Ok("f64"), // finite source-checked arithmetic, not float object semantics
            1 => Ok("u8"),
            2 => Ok("u16"),
            3 => Ok("u32"),
            4 => Ok("u64"),
            5 => Ok("usize"),
            7 => Ok("obj"),
            8 => Ok("tobj"),
            12 => Ok("tagged"),
            t => Err(CompilerError::new(
                RefusalKind::IRType,
                format!(
                    "IR type tag {t} unsupported (supported fixed integers and immutable values)"
                ),
            )),
        }
    }
    pub(super) unsafe fn lit(x: Obj, ty: &str) -> CompilerResult<String> {
        match Self::checked_tag(x, "LitVal")? {
            0 => {
                // A decimal Nat constant in Lean.IR.LitVal.num can be an
                // unbounded runtime object. Preserve its exact source value.
                if matches!(ty, "obj" | "tobj") {
                    let value = Self::decimal_nat(Self::field(x, 0)?)?;
                    return Ok(format!("__LeanValue::nat_from_decimal(\"{value}\")"));
                }
                let n = Self::nat(Self::field(x, 0)?)?;
                if ty == "tagged" {
                    return Ok(format!("__LeanValue::tagged({n})"));
                }
                let max = match ty {
                    "u8" => u8::MAX as usize,
                    "u16" => u16::MAX as usize,
                    "u32" => u32::MAX as usize,
                    "u64" => usize::MAX, // Pinned Linux x86-64 Lean ABI.
                    "usize" => usize::MAX,
                    _ => {
                        return Err(CompilerError::new(
                            RefusalKind::LitVal,
                            format!("literal type {ty} unsupported"),
                        ))
                    }
                };
                if n > max {
                    return Err(CompilerError::new(
                        RefusalKind::LitVal,
                        format!("literal {n} exceeds type {ty}"),
                    ));
                }
                Ok(format!("{n}{ty}"))
            }
            t => Err(CompilerError::new(
                RefusalKind::LitVal,
                format!("literal constructor {t} unsupported"),
            )),
        }
    }
}
