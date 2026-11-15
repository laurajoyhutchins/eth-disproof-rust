//! Deterministic orbit-sparse layout for the appendix's packet *structure*.
//!
//! Unlike uniform source padding, it materializes only occupied orbits
//! under coordinatewise swaps of ordered vertex-label symbol pairs.
//! Every orbit gets its own number of packets. A packet's slot number
//! still determines unequal-symbol orientation and equal-symbol copy
//! index, exactly as in the source construction.
//!
//! **NOT** a replacement tensor coefficient theorem: omitted empty
//! packets, new entry descriptions, canonical lifts, interpolation and
//! source-to-Rust correspondence still require proof.
//!
//! For one orbit with c ordered pair-label classes, q=L/c slots of
//! each class per packet, class loads X_gamma, and max load x:
//!
//!     packets_orbit = ceil(x/q)
//!     padded_slots = L * packets_orbit
//!     imbalance = c*x - sum_gamma X_gamma
//!     rounding = L*packets_orbit - c*x
//!
//! The exact identity P*L = M + total_imbalance + total_rounding
//! proves the packet cap P<=3M/L iff total waste <=2M.
//! The actual per-symbol row/column edge port caps must also be
//! certified separately; sparse layout does not create balance.

use crate::Error;
use crate::two_adic_packet_layout::{BipartiteEdge, PackedPacket};
use std::collections::BTreeMap;

const MAX_EDGES: usize = 256;
const MAX_VERTICES_PER_SHORE: usize = 256;
const MAX_PACKET_SLOTS: usize = 16_384;

fn capacity() -> Error {
    Error::Capacity("bounded orbit-sparse packet layout exceeded capacity".into())
}

fn invalid(message: &'static str) -> Error {
    Error::Invalid(message.into())
}

fn digits(mut number: usize, base: usize, a: usize) -> Vec<usize> {
    let mut result = Vec::with_capacity(a);
    for _ in 0..a {
        result.push(number % base);
        number /= base;
    }
    result
}

/// One occupied coordinatewise-swap orbit. Empty orbits are omitted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrbitPadding {
    pub unordered_pairs: Vec<(usize, usize)>,
    pub real_edges: usize,
    pub ordered_classes_in_orbit: usize,
    pub equal_coordinates: usize,
    pub copies_per_class_per_packet: usize,
    pub maximum_class_load: usize,
    pub packets: usize,
    pub padded_slots: usize,
    /// c * max(X_gamma) - sum(X_gamma), including zero-load orientations.
    pub orientation_imbalance_slots: usize,
    /// L*ceil(max/q) - c*max, caused by the copy-index quantum q.
    pub rounding_slots: usize,
}

/// A concrete orientation/copy-preserving layout and independent receipts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrbitSparsePacketLayout {
    pub r: usize,
    pub a: u32,
    pub slots_per_packet: usize,
    pub packets: Vec<PackedPacket>,
    pub occupied_orbits: Vec<OrbitPadding>,
    pub real_edges: usize,
    pub padded_slots: usize,
    pub unused_slots: usize,
    pub orientation_imbalance_slots: usize,
    pub rounding_slots: usize,
    pub original_maximum_degree: usize,
    pub asserted_degree_cap: usize,
    pub row_ports: Vec<Vec<usize>>,
    pub column_ports: Vec<Vec<usize>>,
    pub child_edge_upper_counts: Vec<Vec<usize>>,
    /// Real packet count obeys P*L <= 3M.
    pub packet_count_bound_holds: bool,
    /// Each coordinate symbol has <= 3M/r real row AND column ports.
    pub symbol_port_bounds_hold: bool,
    /// Every corresponding coordinate-symbol child has <= 6M/r edges.
    pub child_edge_bound_holds: bool,
}

impl OrbitSparsePacketLayout {
    /// These are structural packet/port/degree bounds, not an admission
    /// for the source-defined packet tensors or full counting recursion.
    pub fn original_packet_bounds_hold(&self) -> bool {
        self.packet_count_bound_holds && self.symbol_port_bounds_hold && self.child_edge_bound_holds
    }
}

#[derive(Default)]
struct OrbitWork {
    classes: BTreeMap<(usize, usize), Vec<usize>>,
    real_edges: usize,
}

/// Construct a bounded sparse layout even when the source packet/port
/// *bounds* do not hold. Inspect the explicit booleans before using it.
/// Any invalid graph, degree cap, or size/overflow fails with Error.
///
/// "degree_cap" bounds both original graph degrees and the 2L bound
/// for generated packet vertices. It is *verified*, not assumed.
/// This routine leaves absent orbits absent and does not enumerate D.
pub fn construct_orbit_sparse_bounded(
    edges: &[BipartiteEdge],
    left_labels: &[usize],
    right_labels: &[usize],
    r: usize,
    a: u32,
    degree_cap: usize,
) -> Result<OrbitSparsePacketLayout, Error> {
    if edges.is_empty() || !(2..=64).contains(&r) || a == 0 || a > 3 {
        return Err(invalid("nonempty graph, 2<=r<=64, 1<=a<=3 required"));
    }
    if edges.len() > MAX_EDGES
        || left_labels.len() > MAX_VERTICES_PER_SHORE
        || right_labels.len() > MAX_VERTICES_PER_SHORE
    {
        return Err(capacity());
    }
    let n_coords = usize::try_from(a).map_err(|_| capacity())?;
    let b = r.checked_pow(a).ok_or_else(capacity)?;
    let l = 1usize.checked_shl(a).ok_or_else(capacity)?;
    if degree_cap < l.checked_mul(2).ok_or_else(capacity)? {
        return Err(invalid("new packet vertex degree exceeds supplied cap"));
    }
    if left_labels
        .iter()
        .chain(right_labels)
        .any(|&label| label >= b)
    {
        return Err(invalid("vertex label outside source alphabet"));
    }

    let mut left_degrees = vec![0usize; left_labels.len()];
    let mut right_degrees = vec![0usize; right_labels.len()];
    let mut row_ports = vec![vec![0usize; r]; n_coords];
    let mut column_ports = vec![vec![0usize; r]; n_coords];
    let mut orbits = BTreeMap::<Vec<(usize, usize)>, OrbitWork>::new();

    for (index, edge) in edges.iter().enumerate() {
        if edge.left >= left_labels.len() || edge.right >= right_labels.len() {
            return Err(invalid("edge endpoint outside declared shore"));
        }
        left_degrees[edge.left] += 1;
        right_degrees[edge.right] += 1;

        let left = left_labels[edge.left];
        let right = right_labels[edge.right];
        let rd = digits(left, r, n_coords);
        let cd = digits(right, r, n_coords);
        let signature = rd
            .iter()
            .zip(&cd)
            .map(|(&x, &y)| (x.min(y), x.max(y)))
            .collect::<Vec<_>>();
        for coordinate in 0..n_coords {
            row_ports[coordinate][rd[coordinate]] += 1;
            column_ports[coordinate][cd[coordinate]] += 1;
        }
        let orbit = orbits.entry(signature).or_default();
        orbit.real_edges += 1;
        orbit.classes.entry((left, right)).or_default().push(index);
    }
    let max_degree = left_degrees
        .into_iter()
        .chain(right_degrees)
        .max()
        .unwrap_or(0);
    if max_degree > degree_cap {
        return Err(invalid(
            "original graph maximum degree exceeds supplied cap",
        ));
    }

    let mut packets = Vec::new();
    let mut occupied_orbits = Vec::with_capacity(orbits.len());
    let mut total_imbalance = 0usize;
    let mut total_rounding = 0usize;

    for (signature, orbit) in orbits {
        let equal = signature.iter().filter(|&&(lo, hi)| lo == hi).count();
        let unequal = n_coords - equal;
        let c = 1usize
            .checked_shl(u32::try_from(unequal).map_err(|_| capacity())?)
            .ok_or_else(capacity)?;
        let q = 1usize
            .checked_shl(u32::try_from(equal).map_err(|_| capacity())?)
            .ok_or_else(capacity)?;
        if q.checked_mul(c).ok_or_else(capacity)? != l {
            return Err(invalid(
                "orbit copy and orientation multiplicities mismatch",
            ));
        }
        let maximum = orbit.classes.values().map(Vec::len).max().unwrap_or(0);
        let orbit_packets = maximum.div_ceil(q);
        let padded = orbit_packets.checked_mul(l).ok_or_else(capacity)?;
        let balanced = c.checked_mul(maximum).ok_or_else(capacity)?;
        let imbalance = balanced
            .checked_sub(orbit.real_edges)
            .ok_or_else(|| invalid("orbit class sum exceeded class maximum"))?;
        let rounding = padded
            .checked_sub(balanced)
            .ok_or_else(|| invalid("orbit copy rounding was negative"))?;
        total_imbalance = total_imbalance
            .checked_add(imbalance)
            .ok_or_else(capacity)?;
        total_rounding = total_rounding.checked_add(rounding).ok_or_else(capacity)?;
        if packets
            .len()
            .checked_add(orbit_packets)
            .ok_or_else(capacity)?
            .checked_mul(l)
            .ok_or_else(capacity)?
            > MAX_PACKET_SLOTS
        {
            return Err(capacity());
        }

        for chunk in 0..orbit_packets {
            let mut slots = Vec::with_capacity(l);
            for slot in 0..l {
                let mut row_label = 0usize;
                let mut col_label = 0usize;
                let mut digit_place = 1usize;
                let mut copy_index = 0usize;
                let mut copy_place = 1usize;
                for (coordinate, &(lo, hi)) in signature.iter().enumerate() {
                    let bit = (slot >> coordinate) & 1;
                    let (row_symbol, col_symbol) = if lo == hi {
                        copy_index += bit * copy_place;
                        copy_place *= 2;
                        (lo, hi)
                    } else if bit == 0 {
                        (lo, hi)
                    } else {
                        (hi, lo)
                    };
                    row_label += row_symbol * digit_place;
                    col_label += col_symbol * digit_place;
                    digit_place *= r;
                }
                let source_position = chunk * q + copy_index;
                let edge = orbit
                    .classes
                    .get(&(row_label, col_label))
                    .and_then(|indices| indices.get(source_position))
                    .copied();
                slots.push(edge);
            }
            packets.push(PackedPacket {
                unordered_pairs: signature.clone(),
                slots,
            });
        }
        occupied_orbits.push(OrbitPadding {
            unordered_pairs: signature,
            real_edges: orbit.real_edges,
            ordered_classes_in_orbit: c,
            equal_coordinates: equal,
            copies_per_class_per_packet: q,
            maximum_class_load: maximum,
            packets: orbit_packets,
            padded_slots: padded,
            orientation_imbalance_slots: imbalance,
            rounding_slots: rounding,
        });
    }

    let m = edges.len();
    let padded_slots = packets.len().checked_mul(l).ok_or_else(capacity)?;
    let unused_slots = padded_slots.checked_sub(m).ok_or_else(capacity)?;
    if unused_slots
        != total_imbalance
            .checked_add(total_rounding)
            .ok_or_else(capacity)?
    {
        return Err(invalid("orbit padding waste identity failed"));
    }

    let mut seen = vec![false; m];
    for packet in &packets {
        if packet.unordered_pairs.len() != n_coords || packet.slots.len() != l {
            return Err(invalid("packet dimensions do not match a"));
        }
        for (slot, edge_index) in packet.slots.iter().enumerate() {
            let Some(index) = edge_index else {
                continue;
            };
            if *index >= m || seen[*index] {
                return Err(invalid("packet duplicated or invented a source edge"));
            }
            seen[*index] = true;
            let original = edges[*index];
            let row_digits = digits(left_labels[original.left], r, n_coords);
            let col_digits = digits(right_labels[original.right], r, n_coords);
            for coordinate in 0..n_coords {
                let (lo, hi) = packet.unordered_pairs[coordinate];
                let x = row_digits[coordinate];
                let y = col_digits[coordinate];
                if (x.min(y), x.max(y)) != (lo, hi) {
                    return Err(invalid("packet unordered-symbol signature mismatch"));
                }
                if lo != hi {
                    let orientation = if (slot >> coordinate) & 1 == 0 {
                        (lo, hi)
                    } else {
                        (hi, lo)
                    };
                    if (x, y) != orientation {
                        return Err(invalid("source slot orientation mismatch"));
                    }
                }
            }
        }
    }
    if seen.contains(&false) {
        return Err(invalid("packet layout omitted a source edge"));
    }

    let r_bound = m.checked_mul(3).ok_or_else(capacity)?;
    let r_child_bound = m.checked_mul(6).ok_or_else(capacity)?;
    let mut symbol_port_bounds_hold = true;
    let mut child_edge_bound_holds = true;
    let mut child_edge_upper_counts = vec![vec![0usize; r]; n_coords];
    for coordinate in 0..n_coords {
        for symbol in 0..r {
            let row = row_ports[coordinate][symbol];
            let col = column_ports[coordinate][symbol];
            symbol_port_bounds_hold &= row.checked_mul(r).ok_or_else(capacity)? <= r_bound
                && col.checked_mul(r).ok_or_else(capacity)? <= r_bound;
            let child_edges = row.checked_add(col).ok_or_else(capacity)?;
            child_edge_upper_counts[coordinate][symbol] = child_edges;
            child_edge_bound_holds &=
                child_edges.checked_mul(r).ok_or_else(capacity)? <= r_child_bound;
        }
    }
    let packet_count_bound_holds = padded_slots <= m.checked_mul(3).ok_or_else(capacity)?;
    Ok(OrbitSparsePacketLayout {
        r,
        a,
        slots_per_packet: l,
        packets,
        occupied_orbits,
        real_edges: m,
        padded_slots,
        unused_slots,
        orientation_imbalance_slots: total_imbalance,
        rounding_slots: total_rounding,
        original_maximum_degree: max_degree,
        asserted_degree_cap: degree_cap,
        row_ports,
        column_ports,
        child_edge_upper_counts,
        packet_count_bound_holds,
        symbol_port_bounds_hold,
        child_edge_bound_holds,
    })
}

/// Source packet-lemma *structural* admission only. Failure includes a
/// reason and never treats an arithmetic count as tensor correctness.
pub fn construct_orbit_sparse_admitted(
    edges: &[BipartiteEdge],
    left_labels: &[usize],
    right_labels: &[usize],
    r: usize,
    a: u32,
    degree_cap: usize,
) -> Result<OrbitSparsePacketLayout, Error> {
    let layout =
        construct_orbit_sparse_bounded(edges, left_labels, right_labels, r, a, degree_cap)?;
    if !layout.packet_count_bound_holds {
        return Err(invalid("orbit-sparse packet count exceeds source 3M/L cap"));
    }
    if !layout.symbol_port_bounds_hold {
        return Err(invalid(
            "orbit-sparse symbol port count exceeds source 3M/r cap",
        ));
    }
    if !layout.child_edge_bound_holds {
        return Err(invalid("orbit-sparse child exceeds source 6M/r cap"));
    }
    Ok(layout)
}
