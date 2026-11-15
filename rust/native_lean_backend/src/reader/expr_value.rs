//! Constructors, projections, boxing and sharing observations.
//! Validate source Lean layouts before emitting Rust expressions.
use super::*;

impl Reader {
    pub(super) unsafe fn lower_constructor(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
    ) -> Result<String, String> {
        // Source-pinned zero-field scalar inductives do not allocate a heap.
        // Object constructors retain the independently verified Rc model.
        if matches!(var_ty, "u8" | "usize") {
            // ctor(info, fields). Only nullary scalar constructors are
            // representable without a Lean heap. No field-packing shortcut.
            if !matches!(var_ty, "u8" | "usize") {
                return Err("heap-backed or non-scalar constructor is unsupported".into());
            }
            let info = Self::field(x, 0)?;
            let fields = Self::array(Self::field(x, 1)?)?;
            if !fields.is_empty() {
                return Err("constructor with fields requires an object runtime".into());
            }
            for field in 2..=4 {
                if Self::nat(Self::field(info, field)?)? != 0 {
                    return Err(
                        "constructor with pointer/scalar layout is unsupported".into()
                    );
                }
            }
            let _name = Self::name(Self::field(info, 0)?, 0)?;
            let index = Self::nat(Self::field(info, 1)?)?;
            if index > 255 {
                return Err("constructor tag exceeds nullary enum bound".into());
            }
            return Ok(format!("{index}{var_ty}"));
        }
        // ctor: only immutable, pointer-field constructors with
        // verified metadata. Scalar-field layouts are not yet mapped.
        if !is_value_type(var_ty) {
            return Err("ctor result is not an object-valued IR type".into());
        }
        let info = Self::field(x, 0)?;
        let name = Self::name(Self::field(info, 0)?, 0)?;
        let tag = Self::nat(Self::field(info, 1)?)?;
        let fields = Self::array(Self::field(x, 1)?)?;
        let size = Self::nat(Self::field(info, 2)?)?;
        let usize_count = Self::nat(Self::field(info, 3)?)?;
        let ssize = Self::nat(Self::field(info, 4)?)?;
        if name == "SyncModel.PullIn.mk" {
            if var_ty != "obj"
                || tag != 0
                || size != 4
                || usize_count != 0
                || ssize != 8
                || fields.len() != 4
            {
                return Err(
                    "PullIn.mk requires exact source 4-pointer/8-byte layout".into()
                );
            }
            let mut args = Vec::new();
            for arg in fields {
                args.push(Self::arg(arg, env, "tobj")?);
            }
            return Ok(format!(
                "__LeanValue::pull_in_ctor(vec![{}])",
                args.join(", ")
            ));
        }
        // The source CtorInfo is authoritative: only zero-field
        // tagged variants and heap objects with pointer-only fields
        // are representable. Never pack a scalar field implicitly.
        if !name.contains('.')
            || name.is_empty()
            || tag >= 256
            || size > 1024
            || size != fields.len()
            || usize_count != 0
            || ssize != 0
        {
            return Err(format!(
                "constructor {name} has unsupported scalar, tag or field layout"
            ));
        }
        if size == 0 {
            if var_ty != "tagged" {
                return Err(format!("zero-field constructor {name} is not tagged"));
            }
            return Ok(format!("__LeanValue::tagged({tag})"));
        }
        if var_ty != "obj" {
            return Err("heap constructor has unexpected IR result type".into());
        }
        let mut args = Vec::new();
        for arg in fields {
            args.push(Self::arg(arg, env, "tobj")?);
        }
        if name == "List.cons" {
            return Ok(format!("__LeanValue::list_cons({}, {})", args[0], args[1]));
        }
        Ok(format!(
            "__LeanValue::ctor({tag}, \"{name}\", vec![{}])",
            args.join(", ")
        ))
    }

    pub(super) unsafe fn lower_projection(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
    ) -> Result<String, String> {
        // proj(index, object)
        if !is_value_type(var_ty) {
            return Err("object projection result has non-object type".into());
        }
        let index = Self::nat(Self::field(x, 0)?)?;
        let id = Self::var(Self::field(x, 1)?)?;
        let found = env.get(&id).ok_or("projection of undefined variable")?;
        if !is_value_type(found) {
            return Err("projection from scalar variable".into());
        }
        Ok(format!("x_{id}.field({index})"))
    }

    pub(super) unsafe fn lower_scalar_projection(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
    ) -> Result<String, String> {
        // Lean sproj(n,offset,x): only pinned original PullIn.mk's
        // four object pointers and eight source Bool bytes.
        if var_ty != "u8" {
            return Err("PullIn sproj requires UInt8 result".into());
        }
        let pointers = Self::nat(Self::field(x, 0)?)?;
        let offset = Self::nat(Self::field(x, 1)?)?;
        let id = Self::var(Self::field(x, 2)?)?;
        if pointers != 4 || offset >= 8 || !env.get(&id).is_some_and(|ty| is_value_type(ty))
        {
            return Err(format!(
                "unverified sproj layout n={pointers}, offset={offset}, operand=x_{id}"
            ));
        }
        Ok(format!("x_{id}.pull_in_sproj_u8({pointers}, {offset})"))
    }

    pub(super) unsafe fn lower_box(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
    ) -> Result<String, String> {
        // box(scalar type, variable)
        if !is_value_type(var_ty) {
            return Err("boxed scalar result must be object-valued".into());
        }
        let ty = Self::ty(Self::field(x, 0)?)?;
        if is_value_type(ty) {
            return Err("box expects a scalar IR type".into());
        }
        if ty == "f64" {
            return Err("Float boxing requires an unsupported runtime adapter".into());
        }
        let id = Self::var(Self::field(x, 1)?)?;
        if env.get(&id) != Some(&ty) {
            return Err("box scalar input type mismatch".into());
        }
        Ok(format!("__LeanValue::boxed_{ty}(x_{id})"))
    }

    pub(super) unsafe fn lower_unbox(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
    ) -> Result<String, String> {
        // unbox(object variable) to a statically known scalar.
        if is_value_type(var_ty) {
            return Err("unbox result type must be scalar".into());
        }
        let id = Self::var(Self::field(x, 0)?)?;
        let found = env.get(&id).ok_or("unbox of undefined variable")?;
        if !is_value_type(found) {
            return Err("unbox from non-object variable".into());
        }
        Ok(format!("x_{id}.unbox_{var_ty}()"))
    }

    pub(super) unsafe fn lower_shared_observation(
        x: Obj,
        var_ty: &str,
        env: &BTreeMap<usize, &'static str>,
    ) -> Result<String, String> {
        if var_ty != "u8" {
            return Err("isShared must yield uint8".into());
        }
        let id = Self::var(Self::field(x, 0)?)?;
        if !env.get(&id).is_some_and(|ty| is_value_type(ty)) {
            return Err("isShared requires a value object".into());
        }
        Ok(format!("x_{id}.is_shared()"))
    }

}
