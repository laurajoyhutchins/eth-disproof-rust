//! Case-family validation and branch lowering from Lean IR CtorInfo.
use super::*;

impl Reader {
    // A case arm inherits visible bindings without exporting its own
    // definitions. Every arm still shares the instruction budget and
    // increments nesting depth exactly once.
    unsafe fn lower_case_arm(
        arm: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> CompilerResult<()> {
        let mut arm_env = env.clone();
        Self::body(arm, code, depth + 1, count, &mut arm_env, ret_ty, ctx)
    }

    pub(super) unsafe fn case_body(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> CompilerResult<()> {
        let type_name = Self::name(Self::field(x, 0)?, 0)?;
        match type_name.as_str() {
            "Option" | "List" | "Sum" | "tobj" | "obj" => {
                // The storage type may be erased to obj/tobj. Inspect the
                // actual source CtorInfo, never infer List from a numeric tag.
                let alts = Self::array(Self::field(x, 3)?)?;
                let mut family = None;
                for alt in alts {
                    if Self::checked_tag(alt, "Alt")? != 0 {
                        continue;
                    }
                    let info = Self::field(alt, 0)?;
                    let name = Self::name(Self::field(info, 0)?, 0)?;
                    family = Some(if name.starts_with("Option.") {
                        "Option"
                    } else if name.starts_with("List.") {
                        "List"
                    } else if name.starts_with("Sum.") {
                        "Sum"
                    } else {
                        if matches!(type_name.as_str(), "Option" | "List" | "Sum") {
                            return Err(CompilerError::new(
                                RefusalKind::Alt,
                                format!(
                                "constructor {name} disagrees with source case family {type_name}"
                            ),
                            ));
                        }
                        return Self::generic_object_case(x, code, depth, count, env, ret_ty, ctx);
                    });
                    break;
                }
                let family = family.ok_or(CompilerError::new(
                    RefusalKind::Alt,
                    "object case has no constructor identity",
                ))?;
                if matches!(type_name.as_str(), "Option" | "List" | "Sum") && type_name != family {
                    return Err(CompilerError::new(
                        RefusalKind::Alt,
                        format!(
                        "object case source family {family} contradicts storage type {type_name}"
                    ),
                    ));
                }
                Self::immutable_case(
                    x,
                    code,
                    depth,
                    count,
                    env,
                    ret_ty,
                    ImmutableCaseContext {
                        lowering: ctx,
                        family,
                    },
                )
            }
            _ => {
                let alts = Self::array(Self::field(x, 3)?)?;
                let mut has_bool_constructor = false;
                for alt in alts {
                    if Self::checked_tag(alt, "Alt")? == 0 {
                        let name = Self::name(Self::field(Self::field(alt, 0)?, 0)?, 0)?;
                        has_bool_constructor = name == "Bool.false" || name == "Bool.true";
                        break;
                    }
                }
                if has_bool_constructor {
                    if type_name != "UInt8" {
                        return Err(CompilerError::new(
                            RefusalKind::Alt,
                            "Bool constructor has unexpected IR storage type",
                        ));
                    }
                    Self::boolean_case(x, code, depth, count, env, ret_ty, ctx)
                } else if is_value_type(Self::ty(Self::field(x, 2)?)?) {
                    Self::generic_object_case(x, code, depth, count, env, ret_ty, ctx)
                } else {
                    Self::scalar_enum_case(x, code, depth, count, env, ret_ty, ctx)
                }
            }
        }
    }

    // Data-free inductives may use UInt8 or tagged scalar storage.
    // Constructor identity, not a guessed source datatype, directs patterns.
    pub(super) unsafe fn scalar_enum_case(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> CompilerResult<()> {
        let repr = match Self::checked_tag(Self::field(x, 2)?, "IRType")? {
            1 => "u8",
            12 => {
                return Err(CompilerError::new(
                    RefusalKind::Alt,
                    "object-tagged enum requires a typed object case adapter",
                ))
            }
            _ => {
                return Err(CompilerError::new(
                    RefusalKind::Alt,
                    "non-scalar inductive case is unsupported",
                ))
            }
        };
        let _storage_type = Self::name(Self::field(x, 0)?, 0)?;
        let scrutinee = Self::var(Self::field(x, 1)?)?;
        if env.get(&scrutinee) != Some(&repr) {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "inductive scrutinee storage type mismatch",
            ));
        }
        let alts = Self::array(Self::field(x, 3)?)?;
        if alts.is_empty() || alts.len() > 256 {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "tagged case has unsupported number of alternatives",
            ));
        }
        let mut seen = BTreeSet::new();
        let mut constructor_parent: Option<String> = None;
        let mut default = None;
        writeln!(code, "    match x_{scrutinee} {{").unwrap();
        for alt in alts {
            match Self::checked_tag(alt, "Alt")? {
                0 => {
                    let info = Self::field(alt, 0)?;
                    let name = Self::name(Self::field(info, 0)?, 0)?;
                    let parent = name.rsplit_once('.').map(|(p, _)| p).ok_or_else(|| {
                        CompilerError::new(
                            RefusalKind::Alt,
                            format!("unqualified inductive constructor {name}"),
                        )
                    })?;
                    if let Some(prior) = &constructor_parent {
                        if prior != parent {
                            return Err(CompilerError::new(
                                RefusalKind::Alt,
                                format!(
                                    "mixed inductive constructor families: {prior} and {parent}"
                                ),
                            ));
                        }
                    } else {
                        constructor_parent = Some(parent.to_owned());
                    }
                    let index = Self::nat(Self::field(info, 1)?)?;
                    if index > 255 || !seen.insert(index) {
                        return Err(CompilerError::new(
                            RefusalKind::Alt,
                            format!("invalid or repeated tagged constructor {name}"),
                        ));
                    }
                    writeln!(code, "        {index} => {{").unwrap();
                    Self::lower_case_arm(
                        Self::field(alt, 1)?,
                        code,
                        depth,
                        count,
                        env,
                        ret_ty,
                        ctx,
                    )?;
                    writeln!(code, "        }}").unwrap();
                }
                1 => {
                    if default.replace(Self::field(alt, 0)?).is_some() {
                        return Err(CompilerError::new(
                            RefusalKind::Alt,
                            "multiple tagged default alternatives",
                        ));
                    }
                }
                t => {
                    return Err(CompilerError::new(
                        RefusalKind::Alt,
                        format!("unknown tagged alternative constructor {t}"),
                    ))
                }
            }
        }
        if constructor_parent.is_none() {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "scalar inductive case lacks constructor identity",
            ));
        }
        if let Some(body) = default {
            writeln!(code, "        _ => {{").unwrap();
            Self::lower_case_arm(body, code, depth, count, env, ret_ty, ctx)?;
            writeln!(code, "        }}").unwrap();
        } else {
            writeln!(
                code,
                "        _ => unreachable!(\"invalid tagged enum value\"),"
            )
            .unwrap();
        }
        writeln!(code, "    }}").unwrap();
        Ok(())
    }

    pub(super) unsafe fn immutable_case(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        scoped: ImmutableCaseContext<'_>,
    ) -> CompilerResult<()> {
        let family = scoped.family;
        let ctx = scoped.lowering;
        if !is_value_type(Self::ty(Self::field(x, 2)?)?) {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                format!("{family} case scrutinee must be object-valued"),
            ));
        }
        let id = Self::var(Self::field(x, 1)?)?;
        if !env.get(&id).is_some_and(|ty| is_value_type(ty)) {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                format!("{family} case scrutinee is not object-valued"),
            ));
        }
        let alts = Self::array(Self::field(x, 3)?)?;
        if alts.len() != 2 {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                format!("{family} case requires exactly two constructor alternatives"),
            ));
        }
        // A pinned two-constructor Option/List may have one source Alt.default.
        // Only the *other* source-checked constructor identity is admissible.
        let mut named_index = None;
        let mut defaults = 0usize;
        for alt in &alts {
            match Self::checked_tag(*alt, "Alt")? {
                0 => {
                    let info = Self::field(*alt, 0)?;
                    let name = Self::name(Self::field(info, 0)?, 0)?;
                    let idx = Self::nat(Self::field(info, 1)?)?;
                    immutable_case_ctor(family, idx, &name)
                        .map_err(|error| CompilerError::new(RefusalKind::Alt, error))?;
                    named_index = Some(idx);
                }
                1 => defaults += 1,
                _ => unreachable!(),
            }
        }
        if defaults > 1 || (defaults == 1 && named_index.is_none()) {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                format!("{family} case has unverified default alternatives"),
            ));
        }
        let missing_index = if defaults == 1 {
            Some(1 - named_index.unwrap())
        } else {
            None
        };
        let mut seen = [false; 2];
        writeln!(code, "    match x_{id}.tag() {{").unwrap();
        for alt in alts {
            let is_default = Self::checked_tag(alt, "Alt")? == 1;
            let (name, idx) = if is_default {
                let idx = missing_index.ok_or(CompilerError::new(
                    RefusalKind::Alt,
                    "unexpected default case alternative",
                ))?;
                let name = match (family, idx) {
                    ("Option", 0) => "Option.none",
                    ("Option", 1) => "Option.some",
                    ("List", 0) => "List.nil",
                    ("List", 1) => "List.cons",
                    _ => {
                        return Err(CompilerError::new(
                            RefusalKind::Alt,
                            format!("{family} default case has unknown source layout"),
                        ))
                    }
                };
                (name.to_owned(), idx)
            } else {
                let info = Self::field(alt, 0)?;
                (
                    Self::name(Self::field(info, 0)?, 0)?,
                    Self::nat(Self::field(info, 1)?)?,
                )
            };
            let expected_pointers = immutable_case_ctor(family, idx, &name)
                .map_err(|error| CompilerError::new(RefusalKind::Alt, error))?;
            if seen[idx] {
                return Err(CompilerError::new(
                    RefusalKind::Alt,
                    format!("duplicate {family} case constructor {name} at tag {idx}"),
                ));
            }
            if !is_default {
                let info = Self::field(alt, 0)?;
                let pointer_fields = Self::nat(Self::field(info, 2)?)?;
                let usize_fields = Self::nat(Self::field(info, 3)?)?;
                let scalar_bytes = Self::nat(Self::field(info, 4)?)?;
                if pointer_fields != expected_pointers || usize_fields != 0 || scalar_bytes != 0 {
                    return Err(CompilerError::new(
                        RefusalKind::Alt,
                        format!("{family} alternative {name} has unsupported field layout"),
                    ));
                }
            }
            seen[idx] = true;
            writeln!(code, "        {idx} => {{").unwrap();
            if idx == 0 {
                if family == "List" {
                    writeln!(
                        code,
                        "            assert!(x_{id}.list_is_nil(), \"invalid List.nil representation\");"
                    )
                    .unwrap();
                } else if family == "Sum" {
                    writeln!(code, "            assert!(x_{id}.has_ctor(0, \"Sum.inl\", 1), \"invalid Sum.inl representation\");").unwrap();
                } else {
                    writeln!(
                        code,
                        "            assert!(x_{id}.has_tagged(0), \"invalid Option.none representation\");"
                    )
                    .unwrap();
                }
            } else if family == "List" {
                writeln!(
                    code,
                    "            assert!(x_{id}.list_is_cons(), \"invalid List.cons representation\");"
                )
                .unwrap();
            } else if family == "Sum" {
                writeln!(code, "            assert!(x_{id}.has_ctor(1, \"Sum.inr\", 1), \"invalid Sum.inr representation\");").unwrap();
            } else {
                writeln!(
                    code,
                    "            assert!(x_{id}.has_ctor(1, \"Option.some\", 1), \"invalid Option.some representation\");"
                )
                .unwrap();
            }
            Self::lower_case_arm(
                Self::field(alt, if is_default { 0 } else { 1 })?,
                code,
                depth,
                count,
                env,
                ret_ty,
                ctx,
            )?;
            writeln!(code, "        }}").unwrap();
        }
        if !seen.into_iter().all(|b| b) {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                format!("incomplete {family} case"),
            ));
        }
        writeln!(code, "        _ => unreachable!(\"invalid {family} tag\"),").unwrap();
        writeln!(code, "    }}").unwrap();
        Ok(())
    }

    // A user inductive is accepted only through the actual Lean 4.34.1
    // constructor metadata. The family is source-derived and must agree for
    // every explicit arm; pointer and packed-scalar layouts cannot be mixed.
    pub(super) unsafe fn generic_object_case(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> CompilerResult<()> {
        if !is_value_type(Self::ty(Self::field(x, 2)?)?) {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "user inductive case requires object-valued storage",
            ));
        }
        let id = Self::var(Self::field(x, 1)?)?;
        if !env.get(&id).is_some_and(|ty| is_value_type(ty)) {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "user inductive scrutinee is not object-valued",
            ));
        }
        let alts = Self::array(Self::field(x, 3)?)?;
        if alts.is_empty() || alts.len() > 256 {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "user inductive alternatives exceed reviewed bounds",
            ));
        }
        let mut family: Option<String> = None;
        let mut seen = BTreeSet::new();
        let mut default = false;
        writeln!(code, "    match x_{id}.tag() {{").unwrap();
        for (position, alt) in alts.iter().enumerate() {
            match Self::checked_tag(*alt, "Alt")? {
                0 => {
                    if default {
                        return Err(CompilerError::new(
                            RefusalKind::Alt,
                            "constructor alternative after default",
                        ));
                    }
                    let info = Self::field(*alt, 0)?;
                    let name = Self::name(Self::field(info, 0)?, 0)?;
                    let (parent, _) = name.rsplit_once('.').ok_or_else(|| {
                        CompilerError::new(
                            RefusalKind::Alt,
                            format!("constructor {name} has no family identity"),
                        )
                    })?;
                    if family.as_deref().is_some_and(|f| f != parent) {
                        return Err(CompilerError::new(
                            RefusalKind::Alt,
                            format!("mixed user inductive families: {name}"),
                        ));
                    }
                    family = Some(parent.to_owned());
                    let tag = Self::nat(Self::field(info, 1)?)?;
                    let pointers = Self::nat(Self::field(info, 2)?)?;
                    let usize_fields = Self::nat(Self::field(info, 3)?)?;
                    let scalar_bytes = Self::nat(Self::field(info, 4)?)?;
                    if tag >= 256
                        || pointers > 1024
                        || usize_fields != 0
                        || scalar_bytes != 0
                        || !seen.insert(tag)
                    {
                        return Err(CompilerError::new(
                            RefusalKind::Alt,
                            format!("unsupported or duplicate constructor layout: {name}"),
                        ));
                    }
                    writeln!(code, "        {tag} => {{").unwrap();
                    if pointers == 0 {
                        writeln!(code, "            assert!(x_{id}.has_tagged({tag}), \"invalid nullary constructor representation\");").unwrap();
                    } else {
                        writeln!(code, "            assert!(x_{id}.has_ctor({tag}, \"{name}\", {pointers}), \"invalid object constructor representation\");").unwrap();
                    }
                    Self::lower_case_arm(
                        Self::field(*alt, 1)?,
                        code,
                        depth,
                        count,
                        env,
                        ret_ty,
                        ctx,
                    )?;
                    writeln!(code, "        }}").unwrap();
                }
                1 => {
                    if default || position + 1 != alts.len() || family.is_none() {
                        return Err(CompilerError::new(
                            RefusalKind::Alt,
                            "user inductive default must be unique, last, and source-bound",
                        ));
                    }
                    default = true;
                    writeln!(code, "        _ => {{").unwrap();
                    Self::lower_case_arm(
                        Self::field(*alt, 0)?,
                        code,
                        depth,
                        count,
                        env,
                        ret_ty,
                        ctx,
                    )?;
                    writeln!(code, "        }}").unwrap();
                }
                t => {
                    return Err(CompilerError::new(
                        RefusalKind::Alt,
                        format!("unknown user inductive alternative {t}"),
                    ))
                }
            }
        }
        if family.is_none() {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "user inductive lacks explicit constructor identity",
            ));
        }
        if !default {
            writeln!(
                code,
                "        _ => unreachable!(\"invalid Lean constructor tag\"),"
            )
            .unwrap();
        }
        writeln!(code, "    }}").unwrap();
        Ok(())
    }

    pub(super) unsafe fn boolean_case(
        x: Obj,
        code: &mut String,
        depth: usize,
        count: &mut usize,
        env: &mut BTreeMap<usize, &'static str>,
        ret_ty: &str,
        ctx: LoweringContext<'_>,
    ) -> CompilerResult<()> {
        // Lean 4.34.1 IR uses the *storage type* name UInt8 here,
        // not the source Bool name. Validate Bool constructor names below.
        if Self::name(Self::field(x, 0)?, 0)? != "UInt8" {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "case on a non-UInt8 representation is unsupported",
            ));
        }
        if Self::ty(Self::field(x, 2)?)? != "u8" {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "Bool case must have UInt8 scrutinee",
            ));
        }
        let scrutinee = Self::var(Self::field(x, 1)?)?;
        if env.get(&scrutinee) != Some(&"u8") {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "Bool scrutinee variable is not UInt8",
            ));
        }
        let alts = Self::array(Self::field(x, 3)?)?;
        if alts.len() != 2 {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "Bool case requires exactly two constructor alternatives",
            ));
        }
        let mut seen = [false; 2];
        writeln!(code, "    match x_{scrutinee} {{").unwrap();
        for alt in alts {
            if Self::checked_tag(alt, "Alt")? != 0 {
                return Err(CompilerError::new(
                    RefusalKind::Alt,
                    "Bool default case is not yet supported",
                ));
            }
            let info = Self::field(alt, 0)?;
            let name = Self::name(Self::field(info, 0)?, 0)?;
            let cidx = Self::nat(Self::field(info, 1)?)?;
            let expected = match cidx {
                0 => "Bool.false",
                1 => "Bool.true",
                _ => {
                    return Err(CompilerError::new(
                        RefusalKind::Alt,
                        format!("invalid Bool constructor index {cidx}"),
                    ))
                }
            };
            if name != expected || seen[cidx] {
                return Err(CompilerError::new(
                    RefusalKind::Alt,
                    format!("invalid or repeated Bool alternative {name}"),
                ));
            }
            seen[cidx] = true;
            writeln!(code, "        {cidx} => {{").unwrap();
            // Branch-local variable definitions must never leak across arms.
            Self::lower_case_arm(Self::field(alt, 1)?, code, depth, count, env, ret_ty, ctx)?;
            writeln!(code, "        }}").unwrap();
        }
        if !seen.into_iter().all(|b| b) {
            return Err(CompilerError::new(
                RefusalKind::Alt,
                "incomplete Bool alternatives",
            ));
        }
        writeln!(
            code,
            "        _ => unreachable!(\"invalid Lean Bool tag\"),"
        )
        .unwrap();
        writeln!(code, "    }}").unwrap();
        Ok(())
    }
}
