//! Deterministic bounded simultaneous symbol-port and orbit-packet balancing.
//!
//! Stage 1: for each shore and coordinate, assign vertex symbols by
//! greedy least-loaded bins, weighted by vertex degree.  If the
//! maximum degree is delta and total edge count is M, the load of
//! *every* resulting symbol bin is bounded by
//!
//!     r * load <= M + (r - 1) * delta.
//!
//! Proof: consider the last vertex of weight w assigned to that bin.
//! Before its placement the bin was minimum-loaded, so its load
//! was <= (M - w)/r.  The final bin load is therefore at most
//! M/r + (1 - 1/r) * w <= (M + (r-1)delta)/r.
//!
//! Stage 2: coordinatewise cyclic relabelings on the right shore are
//! bijections of symbol names.  They preserve EVERY per-coordinate
//! real-port load multiset and the old-vertex degree bound, but change
//! orientation-orbit signatures and their exact PL=M+E+R waste.
//! Scan at most a*(r-1)*passes candidates, descending strictly in P.
//!
//! This is a deterministic, polynomial, bounded *candidate constructor*
//! with an EXACT instance-specific structural admission check.  It does
//! NOT prove that a passing orbit-waste labeling exists for every graph,
//! and does not run the appendix's source-defined tensor contraction.

use crate::Error;
use crate::two_adic_orbit_sparse::{OrbitSparsePacketLayout, construct_orbit_sparse_bounded};
use crate::two_adic_packet_layout::BipartiteEdge;
use std::cmp::Reverse;
use std::collections::BTreeMap;

const MAX_VERTICES: usize = 256;
const MAX_EDGES: usize = 256;
const MAX_PASSES: u32 = 3;
const MAX_EVALUATIONS: usize = 1024;

fn invalid(message: &'static str) -> Error {
    Error::Invalid(message.into())
}

fn cap() -> Error {
    Error::Capacity("bounded joint balancing search exceeded capacity".into())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointBalanceReceipt {
    pub r: usize,
    pub a: u32,
    pub left_labels: Vec<usize>,
    pub right_labels: Vec<usize>,
    pub initial_left_labels: Vec<usize>,
    pub initial_right_labels: Vec<usize>,
    /// Absolute cyclic shifts applied to each right-shore digit.
    pub right_coordinate_shifts: Vec<usize>,
    /// Per-candidate full packet layouts evaluated, including initial.
    pub layouts_evaluated: usize,
    pub coordinate_passes: u32,
    pub initial_packets: usize,
    pub initial_unused_slots: usize,
    pub final_packets: usize,
    pub uniform_packets_at_final_labels: Option<u128>,
    pub maximum_degree: usize,
    pub maximum_row_port: usize,
    pub maximum_column_port: usize,
    /// Deterministic greedy theorem's RHS for r*load.
    pub greedy_port_bound_numerator: usize,
    pub greedy_port_sufficient_for_source_limit: bool,
    /// Necessary for ANY labeling: r*Delta <= 3M.
    pub vertex_degree_necessary_port_bound: bool,
    pub final_layout: OrbitSparsePacketLayout,
}

impl JointBalanceReceipt {
    /// Instance-specific structural admission only. This does not
    /// establish tensor entries, precision or recursion correctness.
    pub fn structurally_admitted(&self) -> bool {
        self.final_layout.original_packet_bounds_hold()
    }
}

fn shore_degrees(edges: &[BipartiteEdge], count: usize, left: bool) -> Result<Vec<usize>, Error> {
    let mut degrees = vec![0usize; count];
    for e in edges {
        let vertex = if left { e.left } else { e.right };
        let degree = degrees
            .get_mut(vertex)
            .ok_or_else(|| invalid("edge endpoint outside declared vertex shore"))?;
        *degree = degree.checked_add(1).ok_or_else(cap)?;
    }
    Ok(degrees)
}

/// Independently balance each coordinate's real-port loads. This
/// routine needs no random choices, matching enumerator or SAT oracle.
fn greedy_shore(degree: &[usize], r: usize, a: u32) -> Result<(Vec<usize>, usize), Error> {
    let mut order = (0..degree.len()).collect::<Vec<_>>();
    order.sort_by_key(|&v| (Reverse(degree[v]), v));
    let mut labels = vec![0usize; degree.len()];
    let mut place = 1usize;
    let mut largest = 0usize;
    for coordinate in 0..a {
        let mut loads = vec![0usize; r];
        // A cyclic permutation of tie priority makes independent
        // coordinates non-identical without affecting the proof.
        let preference = usize::try_from(coordinate).map_err(|_| cap())? % r;
        for &vertex in &order {
            let symbol = (0..r)
                .min_by_key(|&s| (loads[s], (s + r - preference) % r))
                .expect("positive r");
            loads[symbol] = loads[symbol].checked_add(degree[vertex]).ok_or_else(cap)?;
            labels[vertex] = labels[vertex]
                .checked_add(symbol.checked_mul(place).ok_or_else(cap)?)
                .ok_or_else(cap)?;
        }
        largest = largest.max(loads.into_iter().max().unwrap_or(0));
        place = place.checked_mul(r).ok_or_else(cap)?;
    }
    Ok((labels, largest))
}

fn rotate_coordinate(
    labels: &[usize],
    r: usize,
    place: usize,
    shift: usize,
) -> Result<Vec<usize>, Error> {
    labels
        .iter()
        .map(|&label| {
            let current = (label / place) % r;
            let next = (current + shift) % r;
            let without = label.checked_sub(current * place).ok_or_else(cap)?;
            without
                .checked_add(next.checked_mul(place).ok_or_else(cap)?)
                .ok_or_else(cap)
        })
        .collect()
}

/// Exact count of source *uniform* packets on the same vertex labels,
/// computed from observed maximum ordered-class load without allocating D.
fn uniform_packet_count(
    edges: &[BipartiteEdge],
    left: &[usize],
    right: &[usize],
    r: usize,
    a: u32,
) -> Option<u128> {
    let b = u128::try_from(r).ok()?.checked_pow(a)?;
    let d = b.checked_mul(b)?;
    let l = 1usize.checked_shl(a)?;
    let mut class_loads = BTreeMap::<(usize, usize), usize>::new();
    for edge in edges {
        let class = (left[edge.left], right[edge.right]);
        let load = class_loads.entry(class).or_default();
        *load = load.checked_add(1)?;
    }
    let maximum = class_loads.values().copied().max().unwrap_or(0);
    let chunks = maximum.div_ceil(l);
    d.checked_mul(u128::try_from(chunks).ok()?)
}

/// A checked polynomial search for a *structurally admitted* candidate.
/// It also returns a failure receipt when the optimized packet count
/// remains above the source 3M/L cap; the caller must inspect the flag.
pub fn construct_joint_balanced_bounded(
    edges: &[BipartiteEdge],
    left_vertices: usize,
    right_vertices: usize,
    r: usize,
    a: u32,
    degree_cap: usize,
    passes: u32,
) -> Result<JointBalanceReceipt, Error> {
    if edges.is_empty()
        || edges.len() > MAX_EDGES
        || left_vertices > MAX_VERTICES
        || right_vertices > MAX_VERTICES
        || !(2..=64).contains(&r)
        || !(1..=3).contains(&a)
        || !(1..=MAX_PASSES).contains(&passes)
    {
        return Err(invalid(
            "nonempty graph <=256 edges and shores, 2<=r<=64, 1<=a<=3, 1..=3 passes required",
        ));
    }
    let l = 1usize.checked_shl(a).ok_or_else(cap)?;
    if degree_cap < 2 * l {
        return Err(invalid("degree cap below required 2L packet degree"));
    }
    let left_degrees = shore_degrees(edges, left_vertices, true)?;
    let right_degrees = shore_degrees(edges, right_vertices, false)?;
    let delta = left_degrees
        .iter()
        .chain(&right_degrees)
        .copied()
        .max()
        .unwrap_or(0);
    if delta > degree_cap {
        return Err(invalid("actual maximum vertex degree exceeds supplied cap"));
    }
    let m = edges.len();
    let degree_numer = (r - 1)
        .checked_mul(delta)
        .and_then(|x| x.checked_add(m))
        .ok_or_else(cap)?;
    let greedy_port_sufficient = (r - 1).checked_mul(delta).ok_or_else(cap)? <= 2 * m;
    let vertex_degree_necessary = r.checked_mul(delta).ok_or_else(cap)? <= 3 * m;
    // A vertex keeps one coordinate digit per coordinate, so a single
    // degree-Delta vertex contributes Delta ports to some symbol bin.
    // This is an actual no-go independent of the labeling algorithm.
    if !vertex_degree_necessary {
        return Err(invalid(
            "unavoidable per-symbol port overload: r*maximum_degree > 3M",
        ));
    }

    let (left_labels, row_max) = greedy_shore(&left_degrees, r, a)?;
    let (mut right_labels, col_max) = greedy_shore(&right_degrees, r, a)?;
    if r.checked_mul(row_max).ok_or_else(cap)? > degree_numer
        || r.checked_mul(col_max).ok_or_else(cap)? > degree_numer
    {
        return Err(invalid("deterministic weighted greedy port theorem failed"));
    }
    let initial_right_labels = right_labels.clone();
    let mut layout =
        construct_orbit_sparse_bounded(edges, &left_labels, &right_labels, r, a, degree_cap)?;
    let initial_packets = layout.packets.len();
    let initial_unused_slots = layout.unused_slots;
    let mut evaluated = 1usize;
    let mut shifts = vec![0usize; usize::try_from(a).map_err(|_| cap())?];
    let mut coordinate_passes = 0u32;
    for _ in 0..passes {
        let mut improved = false;
        let mut place = 1usize;
        for coordinate_shift in &mut shifts {
            let mut best: Option<(usize, Vec<usize>, OrbitSparsePacketLayout)> = None;
            let best_packets = layout.packets.len();
            for shift in 1..r {
                evaluated = evaluated.checked_add(1).ok_or_else(cap)?;
                if evaluated > MAX_EVALUATIONS {
                    return Err(cap());
                }
                let candidate_labels = rotate_coordinate(&right_labels, r, place, shift)?;
                let candidate = construct_orbit_sparse_bounded(
                    edges,
                    &left_labels,
                    &candidate_labels,
                    r,
                    a,
                    degree_cap,
                )?;
                // The current port loads are invariant under a
                // permutation of right-side symbol names. Only P matters.
                let incumbent = best
                    .as_ref()
                    .map_or(best_packets, |(_, _, old)| old.packets.len());
                if candidate.packets.len() < incumbent {
                    best = Some((shift, candidate_labels, candidate));
                }
            }
            if let Some((shift, chosen_labels, chosen_layout)) = best {
                right_labels = chosen_labels;
                layout = chosen_layout;
                *coordinate_shift = (*coordinate_shift + shift) % r;
                improved = true;
            }
            place = place.checked_mul(r).ok_or_else(cap)?;
        }
        coordinate_passes += 1;
        if !improved {
            break;
        }
    }
    if layout.packets.len() > initial_packets {
        return Err(invalid("local search increased packet count"));
    }
    let new_row_max = layout
        .row_ports
        .iter()
        .flat_map(|ports| ports.iter())
        .copied()
        .max()
        .unwrap_or(0);
    let new_col_max = layout
        .column_ports
        .iter()
        .flat_map(|ports| ports.iter())
        .copied()
        .max()
        .unwrap_or(0);
    if new_row_max != row_max || new_col_max != col_max {
        return Err(invalid(
            "digit relabeling modified symbol port multiset maximum",
        ));
    }
    let uniform_packets = uniform_packet_count(edges, &left_labels, &right_labels, r, a);
    if uniform_packets
        .is_some_and(|p| p < u128::try_from(layout.packets.len()).unwrap_or(u128::MAX))
    {
        return Err(invalid(
            "sparse packet count exceeded global uniform padding",
        ));
    }
    Ok(JointBalanceReceipt {
        r,
        a,
        initial_left_labels: left_labels.clone(),
        initial_right_labels,
        left_labels,
        right_labels,
        right_coordinate_shifts: shifts,
        layouts_evaluated: evaluated,
        coordinate_passes,
        initial_packets,
        initial_unused_slots,
        final_packets: layout.packets.len(),
        uniform_packets_at_final_labels: uniform_packets,
        maximum_degree: delta,
        maximum_row_port: new_row_max,
        maximum_column_port: new_col_max,
        greedy_port_bound_numerator: degree_numer,
        greedy_port_sufficient_for_source_limit: greedy_port_sufficient,
        vertex_degree_necessary_port_bound: vertex_degree_necessary,
        final_layout: layout,
    })
}

/// For callers that need the source's packet *structural* inequalities,
/// refuse a search receipt if the best found labeling still violates one.
/// This is not an admission for the source's tensor deformation/recursion.
pub fn construct_joint_balanced_admitted(
    edges: &[BipartiteEdge],
    left_vertices: usize,
    right_vertices: usize,
    r: usize,
    a: u32,
    degree_cap: usize,
    passes: u32,
) -> Result<JointBalanceReceipt, Error> {
    let receipt = construct_joint_balanced_bounded(
        edges,
        left_vertices,
        right_vertices,
        r,
        a,
        degree_cap,
        passes,
    )?;
    if !receipt.structurally_admitted() {
        return Err(invalid(
            "deterministic joint-label search did not certify both packet and port bounds",
        ));
    }
    Ok(receipt)
}
