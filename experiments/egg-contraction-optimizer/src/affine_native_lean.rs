//! Adapted from the already existing native Lean audit on PR #360.
//! This branch retains the independent Lean reference auditor unchanged.
//! The production affine path now crosses the strict raw-value admission
//! gate from PR #360 and independently replays the accepted certificate.
//! This models u8/u64 values, NOT a byte-stream protocol.
//!
//! Generated Lean is data only. Names are emitted as decimal UTF-8 byte
//! lists, never inserted as executable Lean tokens.

use crate::affine::{AffineInterface, AffineRegion, Equation};
use crate::affine_cert::VerificationLimits;
use crate::affine_wire::RawCertificate;
use crate::affine_planner::Stage;
use crate::affine_orders::{fold, generate, Family, Limits, Schedule};

fn list(items: impl IntoIterator<Item = String>) -> String {
    format!("[{}]", items.into_iter().collect::<Vec<_>>().join(", "))
}

fn name_bytes(name: &str) -> String {
    list(name.as_bytes().iter().map(|byte| byte.to_string()))
}

fn names(items: &[String]) -> String {
    list(items.iter().map(|name| name_bytes(name)))
}

fn bool_literal(value: bool) -> &'static str {
    if value { "true" } else { "false" }
}

fn snapshot_literal(
    source: &AffineRegion,
    certificate: &RawCertificate,
    claim: &AffineInterface,
) -> String {
    let equations = list(source.equations.iter().map(|eq| format!(
        "{{ occurrences := {}, rhs := {} }}",
        names(&eq.variables), bool_literal(eq.rhs),
    )));
    let steps = list(certificate.steps.iter().map(|step|
        format!("{{ tag := {}, first := {}, second := {} }}",
            step.tag, step.first, step.second)));
    let pivots = list(certificate.pivot_columns.iter().map(u64::to_string));
    let residual = list(claim.residual.iter().map(|row| format!(
        "{{ columns := {}, rhs := {} }}",
        list(row.boundary_indices.iter().map(usize::to_string)),
        bool_literal(row.rhs),
    )));
    format!(
        "{{ source := {{ internal := {}, boundary := {}, equations := {} }}, \
         cert := {{ version := {}, steps := {}, pivots := {} }}, \
         claim := {{ boundary := {}, residual := {}, rank := {}, free := {}, xors := {} }} }}",
        names(&source.internal), names(&source.boundary), equations,
        certificate.version, steps, pivots, names(&claim.boundary), residual,
        claim.rank, claim.free_internal, claim.elimination_xors,
    )
}

fn emit_case(
    out: &mut String,
    label: &str,
    source: &AffineRegion,
    cert: &RawCertificate,
    claim: &AffineInterface,
    accepted: bool,
    exhaustive: bool,
) {
    let id = out.matches("def native_snapshot_").count();
    let name = format!("native_snapshot_{id}");
    out.push_str(&format!(
        "\n-- {label}\ndef {name} : IndependentETH.AffineNativeAudit.Snapshot :=\n  {}\n",
        snapshot_literal(source, cert, claim),
    ));
    out.push_str(&format!(
        "example : IndependentETH.AffineNativeAudit.audit {name} = {} := by decide\n",
        bool_literal(accepted),
    ));
    if exhaustive {
        out.push_str(&format!(
            "example : IndependentETH.AffineNativeAudit.exhaustiveAgreement {name} = true := by decide\n",
        ));
    }
}

#[derive(Clone)]
struct PortDatum {
    before: Vec<String>,
    next: Vec<String>,
    future: Vec<String>,
    kept: Vec<String>,
    dead: Vec<String>,
}

#[derive(Clone)]
struct OrderedPortDatum {
    scopes: Vec<Vec<String>>,
    order: Vec<usize>,
    output: Vec<String>,
    receipts: Vec<PortDatum>,
}

fn port_plan_literal(w: &OrderedPortDatum) -> String {
    let scopes = list(w.scopes.iter().map(|xs| names(xs)));
    let order = list(w.order.iter().map(usize::to_string));
    let receipts = list(w.receipts.iter().map(|r| format!(
        "{{ before := {}, next := {}, future := {}, kept := {}, dead := {} }}",
        names(&r.before), names(&r.next), names(&r.future),
        names(&r.kept), names(&r.dead),
    )));
    format!(
        "{{ scopes := {scopes}, order := {order}, output := {}, receipts := {receipts} }}",
        names(&w.output),
    )
}

fn emit_plan_case(
    out: &mut String,
    description: &str,
    receipt: &OrderedPortDatum,
    accepted: bool,
) {
    let idx = out.matches("def native_port_plan_").count();
    let name = format!("native_port_plan_{idx}");
    out.push_str(&format!(
        "\n-- {description}\ndef {name} : IndependentETH.AffineNativeAudit.PortPlan :=\n  {}\n",
        port_plan_literal(receipt),
    ));
    out.push_str(&format!(
        "example : IndependentETH.AffineNativeAudit.auditPortPlan {name} = {} := by decide\n",
        bool_literal(accepted),
    ));
}

fn plan_datum(
    factors: &[AffineRegion],
    order: &[usize],
    output: &[String],
    trace: &crate::affine_orders::Trace,
) -> OrderedPortDatum {
    use std::collections::BTreeSet;
    let receipts = (1..order.len()).map(|i| {
        let future = order[i + 1..].iter()
            .flat_map(|&j| factors[j].boundary.iter().cloned())
            .collect::<BTreeSet<_>>();
        PortDatum {
            before: trace.steps[i - 1].retained_ports.clone(),
            next: factors[order[i]].boundary.clone(),
            future: future.into_iter().collect(),
            kept: trace.steps[i].retained_ports.clone(),
            dead: trace.steps[i].newly_dead_ports.clone(),
        }
    }).collect();
    OrderedPortDatum {
        scopes: factors.iter().map(|f| f.boundary.clone()).collect(),
        order: order.to_vec(),
        output: output.to_vec(),
        receipts,
    }
}

fn emit_positive(
    out: &mut String,
    label: &str,
    source: &AffineRegion,
    exhaustive: bool,
) -> Result<(AffineInterface, RawCertificate), String> {
    let (claim, cert) = source.eliminate_with_raw_certificate()?;
    cert.verify(source, &claim, VerificationLimits::default())?;
    emit_case(out, label, source, &cert, &claim, true, exhaustive);
    Ok((claim, cert))
}

/// Emit actual native producer receipts, including each *local* matrix
/// generated by the ordered Stage::merge path. Lean independently rebuilds
/// and replays source equations, and exhaustive-counts small local regions.
pub fn emit_native_lean_fixtures() -> Result<String, String> {
    let mut out = String::from(
        "\n-- Fixed-grammar Lean values from Rust raw-admitted producer.\n\
         -- Native acceptance is NOT used as a trusted proof premise.\n",
    );

    let src = crate::affine::two_equations("b", "c");
    let (claim, cert) = emit_positive(&mut out, "two source XOR equations", &src, true)?;

    let mut broken = cert.clone();
    broken.pivot_columns.clear();
    if broken.verify(&src, &claim, VerificationLimits::default()).is_ok() {
        return Err("raw admission unexpectedly accepted missing pivots".into());
    }
    emit_case(&mut out, "mutated pivot list", &src, &broken, &claim, false, false);

    // Deliberately mutate the *raw u8/u64* values after genuine production.
    // The normal native decoder and the independent Lean reference must
    // both refuse each malformed version, tag, aliased or huge index.
    for (label, mutate) in [
        ("unsupported raw version", 0u8),
        ("invalid raw operation tag", 1u8),
        ("aliased raw row indices", 2u8),
        ("out-of-range u64 row index", 3u8),
        ("out-of-range u64 pivot", 4u8),
    ] {
        let mut invalid = cert.clone();
        match mutate {
            0 => invalid.version = 255,
            1 => invalid.steps[0].tag = 255,
            2 => invalid.steps[0].second = invalid.steps[0].first,
            3 => invalid.steps[0].first = u64::MAX,
            4 => invalid.pivot_columns[0] = u64::MAX,
            _ => unreachable!(),
        }
        if invalid.verify(&src, &claim, VerificationLimits::default()).is_ok() {
            return Err(format!("raw admission unexpectedly accepted {label}"));
        }
        emit_case(&mut out, label, &src, &invalid, &claim, false, false);
    }

    let mut bad_residual = claim.clone();
    if let Some(row) = bad_residual.residual.first_mut() {
        row.rhs = !row.rhs;
        if cert.verify(&src, &bad_residual, VerificationLimits::default()).is_ok() {
            return Err("raw checker accepted altered residual parity".into());
        }
        emit_case(&mut out, "mutated residual parity", &src, &cert, &bad_residual, false, false);
    } else {
        return Err("audit fixture unexpectedly has no residual row".into());
    }

    let mut undeclared = src.clone();
    undeclared.equations[0].variables.push("unregistered".into());
    if cert.verify(&undeclared, &claim, VerificationLimits::default()).is_ok() {
        return Err("raw checker accepted undeclared source occurrence".into());
    }
    emit_case(&mut out, "undeclared occurrence", &undeclared, &cert, &claim, false, false);

    let empty = AffineRegion {
        internal: Vec::new(), boundary: Vec::new(), equations: Vec::new(),
    };
    emit_positive(&mut out, "empty source with no variables", &empty, true)?;

    let free = AffineRegion {
        internal: vec!["u".into(), "unused".into()],
        boundary: vec!["x".into()],
        equations: vec![Equation {
            variables: vec!["u".into(), "x".into()], rhs: true,
        }],
    };
    emit_positive(&mut out, "one unused internal source variable", &free, true)?;

    // The current ordered planner's actual sequence of retained ports
    // drives each merge. The receipt contains exactly the local source
    // region constructed and checked inside Stage::merge_with_receipt.
    for (family, order_kind) in [
        (Family::Chain, Schedule::Sequential),
        (Family::Chain, Schedule::EvenFirst),
        (Family::CirculantXor3, Schedule::Reverse),
    ] {
        let factors = generate(family, 5)?;
        let order = order_kind.indices(factors.len());
        let output: Vec<String> = Vec::new();
        let trace = fold(&factors, &order, &output, &Limits::default())?;
        let mut accumulated = Stage::from_region(&factors[order[0]])?;
        for (i, &next_index) in order.iter().enumerate().skip(1) {
            let next = Stage::from_region(&factors[next_index])?;
            let kept = &trace.steps[i].retained_ports;
            let (merged, merge_source, merge_cert, local_claim) =
                accumulated.merge_with_receipt(&next, kept)?;
            if merged.metrics != trace.steps[i].metrics
                || merged.interface.boundary != *kept
            {
                return Err(format!(
                    "native receipt disagrees with staged fold at {family:?} {order_kind:?} {i}"
                ));
            }
            // Local merge source has at most five internal Boolean ports.
            emit_case(
                &mut out,
                &format!("native merge {family:?} {order_kind:?} step {i}"),
                &merge_source, &merge_cert, &local_claim, true, true,
            );
            accumulated = merged;
        }
        let order_receipt = plan_datum(&factors, &order, &output, &trace);
        emit_plan_case(&mut out,
            &format!("native ordered ports {family:?} {order_kind:?}"),
            &order_receipt, true);
        if family == Family::Chain && order_kind == Schedule::Sequential {
            let mut altered = order_receipt.clone();
            altered.receipts[0].dead.push("invalid".into());
            emit_plan_case(&mut out, "port removal record falsely includes invalid",
                &altered, false);
            let mut altered = order_receipt.clone();
            altered.order[1] = altered.order[0];
            emit_plan_case(&mut out, "duplicate source factor index",
                &altered, false);
            let mut altered = order_receipt.clone();
            altered.receipts[0].future.clear();
            emit_plan_case(&mut out, "omitted future variable support",
                &altered, false);
        }
        if accumulated.interface.boundary != trace.stage.interface.boundary
            || accumulated.interface.free_internal != trace.stage.interface.free_internal
            || accumulated.interface.residual != trace.stage.interface.residual
        {
            return Err("audited native fold differs from actual fold".into());
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::affine_wire::{RawStep, WIRE_VERSION};

    #[test]
    fn native_audit_fixture_emission_includes_real_ordered_merges() {
        let text = emit_native_lean_fixtures().unwrap();
        assert!(text.contains("native merge Chain EvenFirst"));
        assert!(text.contains("native merge CirculantXor3 Reverse"));
        assert!(text.contains("mutated residual parity"));
        assert!(text.contains("out-of-range u64 row index"));
        assert!(text.contains("unsupported raw version"));
        assert!(text.contains("native ordered ports Chain Sequential"));
        assert!(text.contains("duplicate source factor index"));
        assert!(text.contains("auditPortPlan"));
        assert!(text.matches("= true := by decide").count() >= 12);
        assert!(text.matches("= false := by decide").count() >= 3);
    }

    #[test]
    fn hostile_names_remain_data_not_lean_syntax() {
        let source = AffineRegion {
            internal: vec!["x\" : False := by sorry --".into()],
            boundary: Vec::new(), equations: Vec::new(),
        };
        let certificate = RawCertificate {
            version: WIRE_VERSION,
            steps: vec![RawStep { tag: 0, first: 0, second: 1 }],
            pivot_columns: Vec::new(),
        };
        let claim = AffineInterface {
            boundary: Vec::new(), residual: Vec::new(),
            rank: 0, free_internal: 1, elimination_xors: 0,
        };
        let data = snapshot_literal(&source, &certificate, &claim);
        assert!(!data.contains("sorry"));
        assert!(!data.contains("False"));
        assert!(data.contains("120")); // first byte of name
    }
}
