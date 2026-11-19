//! Exact, certificate-checked staged composition of affine boundary interfaces.
//! This is a restricted planner, not an arbitrary factor-network optimizer.
//!
//! Each merge eliminates only ports explicitly designated internal to the
//! merged region. Hidden interiors must be disjoint, and no hidden interior
//! may be exposed as a port in another input.

use crate::affine::{AffineInterface, AffineRegion, Equation};
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StageMetrics {
    /// D: explicit residual equation incidence size plus row and port counts.
    /// This is NOT a minimal circuit size or an asymptotic complexity bound.
    pub d: usize,
    /// B: maximum bit length of any nonzero interface value. For affine
    /// fibers this is free_internal + 1, with 0 if inconsistent everywhere.
    pub b: usize,
    pub ports: usize,
    pub residual_rows: usize,
    pub incidences: usize,
    pub free_internal: usize,
    pub elimination_xors: usize,
    pub certificate_steps: usize,
}

#[derive(Clone, Debug)]
pub struct Stage {
    pub interface: AffineInterface,
    /// Original internal variables whose quantification this stage owns.
    pub hidden: BTreeSet<String>,
    pub metrics: StageMetrics,
}

fn measure(interface: &AffineInterface, steps: usize) -> Result<StageMetrics, String> {
    let incidences = interface.residual.iter().try_fold(0usize, |acc, row| {
        acc.checked_add(row.boundary_indices.len()).ok_or("incidence size overflow")
    })?;
    let d = interface.boundary.len()
        .checked_add(interface.residual.len()).and_then(|x| x.checked_add(incidences))
        .ok_or("interface size overflow")?;
    let b = interface.free_internal.checked_add(1).ok_or("bit length overflow")?;
    Ok(StageMetrics {
        d, b, ports: interface.boundary.len(),
        residual_rows: interface.residual.len(), incidences,
        free_internal: interface.free_internal,
        elimination_xors: interface.elimination_xors,
        certificate_steps: steps,
    })
}

impl Stage {
    pub fn from_region(region: &AffineRegion) -> Result<Self, String> {
        let hidden: BTreeSet<_> = region.internal.iter().cloned().collect();
        if hidden.len() != region.internal.len() {
            return Err("duplicate hidden variable".into());
        }
        let (interface, certificate) = region.eliminate_with_certificate()?;
        let checked = certificate.verify(region, &interface)?;
        let metrics = measure(&interface, checked.operations_checked)?;
        Ok(Self { interface, hidden, metrics })
    }

    /// Merge two independent interiors and sum exactly the ports not retained.
    ///
    /// If F and G are child boundary functions, the result is
    /// H(z) = sum_{x in {0,1}^(ports \ retained)} F(z,x) G(z,x).
    ///
    /// Each child contributes its existing 2^free_internal factor.
    /// The merged affine elimination contributes 2^new_free factor.
    pub fn merge(&self, other: &Self, retained: &[String]) -> Result<Self, String> {
        if !self.hidden.is_disjoint(&other.hidden) {
            return Err("overlapping hidden interiors".into());
        }
        let ports_a: BTreeSet<_> = self.interface.boundary.iter().cloned().collect();
        let ports_b: BTreeSet<_> = other.interface.boundary.iter().cloned().collect();
        let all_ports: BTreeSet<_> = ports_a.union(&ports_b).cloned().collect();
        if !self.hidden.is_disjoint(&all_ports) || !other.hidden.is_disjoint(&all_ports) {
            return Err("hidden variable also exposed as a boundary port".into());
        }
        let kept: BTreeSet<_> = retained.iter().cloned().collect();
        if kept.len() != retained.len() || !kept.is_subset(&all_ports) {
            return Err("retained ports must be unique and present in the merged inputs".into());
        }
        let internal = all_ports.difference(&kept).cloned().collect::<Vec<_>>();
        let boundary = retained.to_vec();
        let mut equations = Vec::new();
        for interface in [&self.interface, &other.interface] {
            for row in &interface.residual {
                let variables = row.boundary_indices.iter()
                    .map(|&index| interface.boundary.get(index)
                        .cloned().ok_or("invalid residual port index"))
                    .collect::<Result<Vec<_>, _>>()?;
                equations.push(Equation { variables, rhs: row.rhs });
            }
        }
        let region = AffineRegion { internal, boundary, equations };
        let (mut interface, certificate) = region.eliminate_with_certificate()?;
        let checked = certificate.verify(&region, &interface)?;
        interface.free_internal = interface.free_internal
            .checked_add(self.interface.free_internal)
            .and_then(|x| x.checked_add(other.interface.free_internal))
            .ok_or("multiplicity exponent overflow")?;
        let metrics = measure(&interface, checked.operations_checked)?;
        let hidden = self.hidden.union(&other.hidden)
            .cloned().chain(region.internal).collect();
        Ok(Self { interface, hidden, metrics })
    }

    pub fn count_at(&self, boundary: &BTreeMap<String, bool>) -> Result<BigUint, String> {
        self.interface.evaluate(boundary)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn region(internal: &[&str], boundary: &[&str], rows: &[(&[&str], bool)]) -> AffineRegion {
        AffineRegion {
            internal: internal.iter().map(|s| s.to_string()).collect(),
            boundary: boundary.iter().map(|s| s.to_string()).collect(),
            equations: rows.iter().map(|(vars, rhs)| Equation {
                variables: vars.iter().map(|s| s.to_string()).collect(), rhs: *rhs,
            }).collect(),
        }
    }

    fn oracle(regions: &[&AffineRegion], retained: &[&str], assignment: usize) -> BigUint {
        let mut all = BTreeSet::new();
        for r in regions {
            all.extend(r.internal.iter().cloned());
            all.extend(r.boundary.iter().cloned());
        }
        let fixed: BTreeMap<_, _> = retained.iter().enumerate()
            .map(|(i, s)| (s.to_string(), assignment & (1 << i) != 0)).collect();
        let free = all.into_iter().filter(|v| !fixed.contains_key(v)).collect::<Vec<_>>();
        assert!(free.len() <= 16);
        let mut count = BigUint::from(0u8);
        for mask in 0..(1usize << free.len()) {
            let mut bits = fixed.clone();
            for (i, var) in free.iter().enumerate() {
                bits.insert(var.clone(), mask & (1 << i) != 0);
            }
            if regions.iter().flat_map(|r| &r.equations).all(|eq| {
                eq.variables.iter().fold(false, |parity, v| parity ^ bits[v]) == eq.rhs
            }) {
                count += 1u8;
            }
        }
        count
    }

    #[test]
    fn three_region_chain_eliminates_shared_ports_without_tables() {
        let a = region(&["u"], &["x", "y"], &[
            (&["u", "x"] as &[&str], false),
            (&["u", "y"], false),
        ]);
        let b = region(&["v"], &["y", "z"], &[
            (&["v", "y"], true),
            (&["v", "z"], false),
        ]);
        let c = region(&["w"], &["z", "t"], &[
            (&["w", "z"], false),
            (&["w", "t"], false),
        ]);
        let sa = Stage::from_region(&a).unwrap();
        let sb = Stage::from_region(&b).unwrap();
        let sc = Stage::from_region(&c).unwrap();
        let ab = sa.merge(&sb, &["x".into(), "z".into()]).unwrap();
        let abc = ab.merge(&sc, &["x".into(), "t".into()]).unwrap();
        let alternative = sb.merge(&sc, &["y".into(), "t".into()]).unwrap();
        let abc_alt = sa.merge(&alternative, &["x".into(), "t".into()]).unwrap();
        for mask in 0..4 {
            let bits = BTreeMap::from([
                ("x".into(), mask & 1 != 0),
                ("t".into(), mask & 2 != 0),
            ]);
            let expected = oracle(&[&a, &b, &c], &["x", "t"], mask);
            assert_eq!(abc.count_at(&bits).unwrap(), expected);
            assert_eq!(abc_alt.count_at(&bits).unwrap(), expected);
        }
        assert_eq!(abc.metrics.ports, 2);
        assert_eq!(abc.metrics.b, abc.interface.free_internal + 1);
        assert_eq!(abc.metrics.d, abc.metrics.ports + abc.metrics.residual_rows + abc.metrics.incidences);
    }

    #[test]
    fn multiplicity_and_contradictions_survive_merging() {
        let a = region(&["u", "free"], &["x"], &[
            (&["u", "x"] as &[&str], false),
        ]);
        let b = region(&["v"], &["x"], &[
            (&["v", "x"] as &[&str], false),
        ]);
        let sa = Stage::from_region(&a).unwrap();
        let sb = Stage::from_region(&b).unwrap();
        let merged = sa.merge(&sb, &[]).unwrap();
        assert_eq!(merged.count_at(&BTreeMap::new()).unwrap(), 8u8.into());
        assert_eq!(merged.interface.free_internal, 3);
        let contradiction = region(&[], &["x"], &[
            (&["x"] as &[&str], true),
            (&["x"], false),
        ]);
        let bad = sa.merge(&Stage::from_region(&contradiction).unwrap(), &[]).unwrap();
        assert_eq!(bad.count_at(&BTreeMap::new()).unwrap(), 0u8.into());
    }

    #[test]
    fn invalid_seams_refuse() {
        let a = Stage::from_region(&region(&["u"], &["x"], &[])).unwrap();
        let b = Stage::from_region(&region(&["u"], &["y"], &[])).unwrap();
        assert!(a.merge(&b, &[]).unwrap_err().contains("overlapping"));
        let c = Stage::from_region(&region(&["v"], &["u"], &[])).unwrap();
        assert!(a.merge(&c, &[]).unwrap_err().contains("exposed"));
        assert!(a.merge(&c, &["unknown".into()]).is_err());
    }
}
