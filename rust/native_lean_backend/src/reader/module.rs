//! Emission of exact Lean declarations and requested-root dependency closure.
use super::*;

impl Reader {
    pub(crate) unsafe fn emit(decl: Obj, rust_name: Obj) -> CompilerResult<String> {
        if lr_abi_probe() == 0 {
            return Err(CompilerError::new(
                RefusalKind::Abi,
                "Lean C ABI runtime probe failed",
            ));
        }
        let declaration = Self::name(Self::field(decl, 0)?, 0)?;
        let features = Cell::new(RuntimeFeatures::default());
        let generated = Self::emit_function(decl, &Self::string(rust_name)?, None, None, &features)
            .map_err(|reason| reason.with_declaration(declaration))?;
        include_value_runtime(generated, features.get())
    }

    pub(super) unsafe fn emit_function(
        decl: Obj,
        rust_name: &str,
        functions: Option<&FunctionTable>,
        ownership: Option<&OwnershipSummary>,
        features: &Cell<RuntimeFeatures>,
    ) -> CompilerResult<String> {
        if Self::checked_tag(decl, "Decl")? != 0 {
            return Err(CompilerError::new(
                RefusalKind::Decl,
                "extern declaration without executable body",
            ));
        }
        let declared_name = Self::name(Self::field(decl, 0)?, 0)?;
        if rust_name.is_empty()
            || !rust_name.as_bytes()[0].is_ascii_alphabetic()
            || !rust_name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_')
        {
            return Err(CompilerError::new(
                RefusalKind::Decl,
                "unsafe Rust function name",
            ));
        }
        const KEYWORDS: &[&str] = &[
            "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum",
            "extern", "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod",
            "move", "mut", "pub", "ref", "return", "self", "Self", "static", "struct", "super",
            "trait", "true", "type", "unsafe", "use", "where", "while", "abstract", "become",
            "box", "gen", "try", "typeof", "unsized", "virtual", "yield",
        ];
        if KEYWORDS.contains(&rust_name) || rust_name == "_" {
            return Err(CompilerError::new(
                RefusalKind::Decl,
                "reserved Rust function name",
            ));
        }
        let params = Self::array(Self::field(decl, 1)?)?;
        let ret = Self::ty(Self::field(decl, 2)?)?;
        let body = Self::field(decl, 3)?;
        if is_value_type(ret) {
            RuntimeFeatures::mark(features, RuntimeFeatures::VALUE);
        }
        let shared = Self::shared_observations(body)?;
        // Preserve Lean source CFG order through calls, branches, and joins.
        // Object-returning COW helpers remain value-only, not physical proofs.
        let can_observe =
            !shared.is_empty() || ownership.is_some_and(|s| s.may_observe.contains(&declared_name));
        if can_observe && Self::rc_may_precede_sharedness(body, ownership)? {
            return Err(CompilerError::new(
                RefusalKind::Decl,
                "unverified isShared after source inc/dec/del reference bookkeeping or interprocedural call",
            ));
        }
        if let Some(summary) = ownership {
            if Self::captures_observer(body, summary)? {
                return Err(CompilerError::new(
                    RefusalKind::Decl,
                    "unverified isShared through closure capture and indirect application",
                ));
            }
        }
        // Admit only borrowed-parameter ownership transfers justified by
        // source IR inc operations. This is a bounded direct-variable audit;
        // it does not certify derived aliases or every heap event.
        let mut borrowed = Vec::new();
        for param in &params {
            let id = Self::var(Self::field(*param, 0)?)?;
            let ty = Self::ty(Self::field(*param, 1)?)?;
            if is_value_type(ty) && Self::param_borrow(*param)? {
                borrowed.push(id);
            }
        }
        Self::verify_direct_borrow_transfers(body, &borrowed, functions)?;
        // Rust Rc handles may keep a projected allocation memory-safe after
        // the Lean source has released its last protecting parent reference.
        // Check source parent/child lifetimes independently of Rust Rc counts.
        let mut lifetime_formals = Vec::new();
        for param in &params {
            let ty = Self::ty(Self::field(*param, 1)?)?;
            if is_value_type(ty) {
                lifetime_formals.push((
                    Self::var(Self::field(*param, 0)?)?,
                    Self::param_borrow(*param)?,
                ));
            }
        }
        Self::verify_projected_lifetimes(body, &lifetime_formals, functions)?;

        let mut env = BTreeMap::new();
        let clean_name = declared_name.replace(['\n', '\r'], "_");
        let mut result = format!("// Generated directly from Lean IR declaration: {clean_name}\n");
        // Preserve the explicit terminal forms from Lean IR, including in
        // nested join and branch bodies. This is intentional generated code.
        result.push_str("#[allow(clippy::needless_return)]\n");
        write!(result, "pub fn {rust_name}(").unwrap();
        for (i, param) in params.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            let var = Self::var(Self::field(*param, 0)?)?;
            let ty = Self::ty(Self::field(*param, 1)?)?;
            if is_value_type(ty) {
                RuntimeFeatures::mark(features, RuntimeFeatures::VALUE);
            }
            if Self::param_borrow(*param)? && shared.contains(&var) {
                return Err(CompilerError::new(
                    RefusalKind::Decl,
                    format!(
                        "borrowed parameter x_{var} has unverified isShared ownership semantics"
                    ),
                ));
            }
            if env.insert(var, ty).is_some() {
                return Err(CompilerError::new(
                    RefusalKind::Decl,
                    format!("duplicate parameter x_{var}"),
                ));
            }
            write!(result, "x_{var}: {}", rust_type(ty)).unwrap();
        }
        writeln!(result, ") -> {} {{", rust_type(ret)).unwrap();
        Self::body(
            body,
            &mut result,
            0,
            &mut 0,
            &mut env,
            ret,
            LoweringContext {
                functions,
                joins: &JoinTable::new(),
                features,
            },
        )?;
        result.push_str("}\n");
        Ok(result)
    }
    pub(super) unsafe fn signature(decl: Obj) -> CompilerResult<Signature> {
        if Self::checked_tag(decl, "Decl")? != 0 {
            return Err(CompilerError::new(
                RefusalKind::Decl,
                "extern or opaque declaration in native dependency closure",
            ));
        }
        let mut params = Vec::new();
        let mut borrows = Vec::new();
        let mut formal_ids = Vec::new();
        for param in Self::array(Self::field(decl, 1)?)? {
            formal_ids.push(Self::var(Self::field(param, 0)?)?);
            borrows.push(Self::param_borrow(param)?);
            params.push(Self::ty(Self::field(param, 1)?)?);
        }
        let result = Self::ty(Self::field(decl, 2)?)?;
        // Source-exact identity return: the entire body returns an owned
        // object formal unchanged. No preceding calls, mutation, or RC ops.
        // A general call-result alias is never inferred from its type.
        let returned_owned_formal = if is_value_type(result) {
            match Self::body_view(Self::field(decl, 3)?)? {
                FnBodyView::Return { value } if Self::checked_tag(value, "Arg")? == 0 => {
                    let source = Self::var(Self::field(value, 0)?)?;
                    formal_ids.iter().enumerate().find_map(|(i, id)| {
                        (*id == source && !borrows[i] && is_value_type(params[i]))
                            .then_some(i)
                    })
                }
                _ => None,
            }
        } else {
            None
        };
        Ok(Signature {
            params,
            borrows,
            result,
            returned_owned_formal,
        })
    }

    // Source-bound, iterative reachability of directly called functions.
    pub(super) unsafe fn body_calls(x: Obj, calls: &mut BTreeSet<String>) -> CompilerResult<()> {
        let mut pending = vec![x];
        let mut count = 0;
        while let Some(body) = pending.pop() {
            count += 1;
            if count > 100_000 {
                return Err(CompilerError::new(
                    RefusalKind::Dependency,
                    "dependency IR traversal exceeded 100000 instructions",
                ));
            }
            match Self::body_view(body)? {
                FnBodyView::Decl { expr, next, .. } => {
                    if matches!(Self::checked_tag(expr, "Expr")?, 6 | 7) {
                        calls.insert(Self::name(Self::field(expr, 0)?, 0)?);
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
        Ok(())
    }

    pub(crate) unsafe fn emit_module(
        decls: Obj,
        root: Obj,
        public_name: Obj,
    ) -> CompilerResult<String> {
        let root = Self::name(root, 0)?;
        let public_name = Self::string(public_name)?;
        Self::emit_roots(decls, vec![(root, public_name)])
    }

    pub(crate) unsafe fn emit_module_many(decls: Obj, roots: Obj) -> CompilerResult<String> {
        let mut public_roots = Vec::new();
        for item in Self::array(roots)? {
            let root = Self::name(item, 0)?;
            // In v1 we expose the final Lean identifier as the Rust public API.
            // Any collisions (e.g. Foo.run and Bar.run) must refuse.
            let public = root.rsplit('.').next().unwrap_or("").to_owned();
            public_roots.push((root, public));
        }
        Self::emit_roots(decls, public_roots)
    }

    pub(super) unsafe fn emit_roots(
        decls: Obj,
        roots: Vec<(String, String)>,
    ) -> CompilerResult<String> {
        if lr_abi_probe() == 0 {
            return Err(CompilerError::new(
                RefusalKind::Abi,
                "Lean C ABI runtime probe failed",
            ));
        }
        if roots.is_empty() || roots.len() > 128 {
            return Err(CompilerError::new(
                RefusalKind::Dependency,
                "expected 1..128 public Lean root declarations",
            ));
        }
        let entries = Self::array(decls)?;
        let mut definitions = BTreeMap::<String, Obj>::new();
        for decl in entries {
            let name = Self::name(Self::field(decl, 0)?, 0)?;
            if definitions.insert(name.clone(), decl).is_some() {
                return Err(CompilerError::new(
                    RefusalKind::Dependency,
                    format!("duplicate IR declaration in closure: {name}"),
                ));
            }
        }
        let mut pending = Vec::new();
        let mut public_names = BTreeSet::new();
        let mut root_names = BTreeSet::new();
        for (root, public) in &roots {
            if !root_names.insert(root.clone()) {
                return Err(CompilerError::new(
                    RefusalKind::Dependency,
                    format!("duplicate public Lean root: {root}"),
                ));
            }
            if !public_names.insert(public.clone()) {
                return Err(CompilerError::new(
                    RefusalKind::Dependency,
                    format!("duplicate Rust public API name: {public}"),
                ));
            }
            if !definitions.contains_key(root) {
                return Err(CompilerError::new(
                    RefusalKind::Dependency,
                    format!("requested Lean root {root} has no compiler IR"),
                ));
            }
            pending.push(root.clone());
        }
        let mut visited = BTreeSet::<String>::new();
        let mut closure = BTreeMap::<String, Obj>::new();
        let mut signatures = FunctionTable::new();
        while let Some(name) = pending.pop() {
            if !visited.insert(name.clone()) {
                continue;
            }
            if visited.len() > 2048 {
                return Err(CompilerError::new(
                    RefusalKind::ResourceLimit,
                    "native declaration closure exceeds 2048 functions",
                ));
            }
            let decl = *definitions.get(&name).ok_or_else(|| CompilerError::new(RefusalKind::Dependency, format!("dependency {name} has no compiled IR in the current module; no external fallback")))?;
            let sig = Self::signature(decl).map_err(|e| e.with_context(&name))?;
            let mut called = BTreeSet::new();
            Self::body_calls(Self::field(decl, 3)?, &mut called)?;
            for callee in called {
                if !is_primitive(&callee) {
                    pending.push(callee);
                }
            }
            signatures.insert(name.clone(), sig);
            closure.insert(name, decl);
        }
        let ownership = Self::ownership_summary(&closure)?;
        let features = Cell::new(RuntimeFeatures::default());
        let mut result = String::from(
            "// Native in-process Lean IR closure; no JSON or Lean runtime dependency.\n",
        );
        for (name, decl) in &closure {
            result.push_str(&Self::emit_function(
                *decl,
                &internal_name(name),
                Some(&signatures),
                Some(&ownership),
                &features,
            )?);
            result.push('\n');
        }
        // Only callable object ABI declarations receive generated thunks.
        // No raw address is ever read out of a Lean or Rust heap object.
        for (name, sig) in &signatures {
            if sig.params.is_empty()
                || !sig.params.iter().all(|ty| is_value_type(ty))
                || !is_value_type(sig.result)
            {
                continue;
            }
            // Full-application helpers can take stack arguments directly
            // when one source AP operand remains. The original Vec thunk
            // remains available for general PAPs and multi-arg applications.
            if sig.params.len() == 2 {
                result.push_str("#[allow(dead_code)]\n");
                writeln!(
                    result,
                    "fn {}_binary(capture: __LeanValue, arg: __LeanValue) -> __LeanValue {{",
                    internal_closure_name(name)
                )
                .unwrap();
                writeln!(result, "    {}(capture, arg)\n}}", internal_name(name)).unwrap();
            }
            if sig.params.len() == 3 {
                result.push_str("#[allow(dead_code)]\n");
                writeln!(
                    result,
                    "fn {}_ternary(a: __LeanValue, b: __LeanValue, c: __LeanValue) -> __LeanValue {{",
                    internal_closure_name(name)
                ).unwrap();
                writeln!(result, "    {}(a, b, c)\n}}", internal_name(name)).unwrap();
            }
            result.push_str("#[allow(dead_code)]\n");
            writeln!(
                result,
                "fn {}(args: Vec<__LeanValue>) -> __LeanValue {{",
                internal_closure_name(name)
            )
            .unwrap();
            writeln!(result, "    assert_eq!(args.len(), {});", sig.params.len()).unwrap();
            write!(result, "    {}(", internal_name(name)).unwrap();
            for i in 0..sig.params.len() {
                if i > 0 {
                    result.push_str(", ");
                }
                write!(result, "args[{i}].compiler_alias()").unwrap();
            }
            result.push_str(")\n}\n");
        }
        // Exact same dependency closure is shared by all public wrappers.
        for (root, public_name) in roots {
            let sig = signatures.get(&root).ok_or(CompilerError::new(
                RefusalKind::Dependency,
                "requested root missing from closure",
            ))?;
            // Validate the identifier, including Rust reserved words.
            let _ = Self::emit_function(
                *closure.get(&root).unwrap(),
                &public_name,
                Some(&signatures),
                Some(&ownership),
                &features,
            )?;
            // Preserve the original Lean root name as the public API; Rust's
            // naming lint must not force an observable symbol rename.
            result.push_str("#[allow(non_snake_case)]\n");
            write!(result, "pub fn {public_name}(").unwrap();
            for (i, ty) in sig.params.iter().enumerate() {
                if i > 0 {
                    result.push_str(", ");
                }
                write!(result, "p_{i}: {}", rust_type(ty)).unwrap();
            }
            write!(
                result,
                ") -> {} {{\n    {}(",
                rust_type(sig.result),
                internal_name(&root)
            )
            .unwrap();
            for i in 0..sig.params.len() {
                if i > 0 {
                    result.push_str(", ");
                }
                write!(result, "p_{i}").unwrap();
            }
            result.push_str(")\n}\n");
        }
        include_value_runtime(result, features.get())
    }
}
