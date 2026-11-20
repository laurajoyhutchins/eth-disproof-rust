//! Conservative source-event order comparison for a single emitted Rust function.
//!
//! This is an emitter sanity gate for straight-line, source-derived Lean IR,
//! not a Rust parser, alias analysis, runtime simulation, or effect-proof engine.
//! Unrecognized syntactic forms of the selected operations refuse the receipt.

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Event {
    Inc {
        var: usize,
        count: usize,
        checked: bool,
        persistent: bool,
    },
    Dec {
        var: usize,
        count: usize,
        checked: bool,
        persistent: bool,
    },
    Delete {
        var: usize,
    },
    Observe {
        result: usize,
        var: usize,
    },
}

fn rust_var(token: &str) -> Result<usize, &'static str> {
    token
        .strip_prefix("x_")
        .filter(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
        .and_then(|digits| digits.parse::<usize>().ok())
        .ok_or("expected canonical source variable x_<decimal>")
}

fn flags(source: &str) -> Result<(usize, bool, bool), &'static str> {
    let [count, checked, persistent] = source
        .split(", ")
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| "expected count and two Boolean flags")?;
    let count = count
        .parse::<usize>()
        .map_err(|_| "invalid source reference delta")?;
    let checked = match checked {
        "true" => true,
        "false" => false,
        _ => return Err("invalid checked flag"),
    };
    let persistent = match persistent {
        "true" => true,
        "false" => false,
        _ => return Err("invalid persistent flag"),
    };
    Ok((count, checked, persistent))
}

fn emitted_events(generated: &str) -> Result<Vec<Event>, &'static str> {
    let mut events = Vec::new();
    for line in generated.lines().map(str::trim) {
        if line.contains(".source_inc(") || line.contains(".source_dec(") {
            let (object, call) = line
                .split_once('.')
                .ok_or("malformed source reference instruction")?;
            let var = rust_var(object)?;
            let (is_inc, args) = if let Some(args) = call.strip_prefix("source_inc(") {
                (true, args)
            } else if let Some(args) = call.strip_prefix("source_dec(") {
                (false, args)
            } else {
                return Err("unexpected source reference instruction");
            };
            let args = args
                .strip_suffix(");")
                .ok_or("invalid source reference call termination")?;
            let (count, checked, persistent) = flags(args)?;
            events.push(if is_inc {
                Event::Inc {
                    var,
                    count,
                    checked,
                    persistent,
                }
            } else {
                Event::Dec {
                    var,
                    count,
                    checked,
                    persistent,
                }
            });
        } else if line.contains(".source_del(") {
            let (object, call) = line.split_once('.').ok_or("malformed source deletion")?;
            if call != "source_del();" {
                return Err("invalid shell deletion syntax");
            }
            events.push(Event::Delete {
                var: rust_var(object)?,
            });
        } else if line.contains(".is_shared(") {
            let declaration = line
                .strip_prefix("let ")
                .ok_or("unexpected sharing observation")?;
            let (result, call) = declaration
                .split_once(" = ")
                .ok_or("sharing observation without binding")?;
            let result = rust_var(
                result
                    .strip_suffix(": u8")
                    .ok_or("sharing result must be u8")?,
            )?;
            events.push(Event::Observe {
                result,
                var: rust_var(
                    call.strip_suffix(".is_shared();")
                        .ok_or("invalid sharing expression")?,
                )?,
            });
        } else if line.contains(".source_") || line.contains(".is_shared") {
            return Err("unrecognized source ownership operation in emitted Rust");
        }
    }
    Ok(events)
}

pub(super) fn verify_emitted_order(
    expected: &[Event],
    generated: &str,
) -> Result<(), &'static str> {
    let actual = emitted_events(generated)?;
    if actual != expected {
        return Err("emitted source reference events differ in identity, arguments, or order");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source() -> Vec<Event> {
        vec![
            Event::Observe { result: 3, var: 2 },
            Event::Inc {
                var: 2,
                count: 1,
                checked: true,
                persistent: false,
            },
            Event::Dec {
                var: 2,
                count: 1,
                checked: false,
                persistent: false,
            },
            Event::Delete { var: 2 },
        ]
    }

    fn emitted() -> &'static str {
        "// Generated directly from Lean IR declaration: Demo\n\
         pub fn foo(x_2: __LeanValue) -> u8 {\n\
             let x_3: u8 = x_2.is_shared();\n\
             x_2.source_inc(1, true, false);\n\
             x_2.source_dec(1, false, false);\n\
             x_2.source_del();\n\
             x_3\n}\n"
    }

    #[test]
    fn accepts_exact_source_order() {
        assert!(verify_emitted_order(&source(), emitted()).is_ok());
    }

    #[test]
    fn refuses_reordered_observation() {
        let bad = emitted().replace(
            "let x_3: u8 = x_2.is_shared();\nx_2.source_inc(1, true, false);",
            "x_2.source_inc(1, true, false);\nlet x_3: u8 = x_2.is_shared();",
        );
        assert_ne!(bad, emitted());
        assert!(verify_emitted_order(&source(), &bad).is_err());
    }

    #[test]
    fn refuses_missing_or_extra_effect() {
        assert!(
            verify_emitted_order(&source(), &emitted().replace("x_2.source_del();", "")).is_err()
        );
        assert!(verify_emitted_order(
            &source(),
            &emitted().replace(
                "x_2.source_del();",
                "x_2.source_inc(1, true, false);\nx_2.source_del();"
            )
        )
        .is_err());
    }

    #[test]
    fn refuses_alias_or_flag_relabeling() {
        for bad in [
            emitted().replace("x_2.source_inc", "x_7.source_inc"),
            emitted().replace("source_inc(1, true, false)", "source_inc(1, false, false)"),
            emitted().replace("x_3: u8", "x_4: u8"),
            emitted().replace("source_dec(1, false, false)", "source_dec(2, false, false)"),
        ] {
            assert!(verify_emitted_order(&source(), &bad).is_err());
        }
    }

    #[test]
    fn refuses_noncanonical_ownership_syntax() {
        for extra in [
            "x_2.source_inc(unknown, true, false);",
            "x_2.source_dec(1, maybe, false);",
            "x_2.source_del(1);",
            "let x_9: u8 = x_2.is_shared(1);",
            "x_2.source_reset();",
        ] {
            assert!(
                verify_emitted_order(&source(), &format!("{}\n{extra}", emitted())).is_err(),
                "{extra}"
            );
        }
    }
}
