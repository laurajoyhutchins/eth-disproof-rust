//! Bounded construction of the original packet *layout* from vertex labels.
//!
//! This preserves the source's class padding and orientation-by-slot rule.
//! No tensor entries, interpolation, or 2-adic recursion are implemented.
//! It accepts explicit actual-load certificates even when a conservative
//! sufficient labeling inequality does not hold, but verifies all the
//! packet lemma's *concrete* load, degree and child-edge conclusions.
//!
//! The source constructs packets from all ordered symbol-pair classes with
//! equal H_pad multiple-of-L loads. For each unordered coordinate pair,
//! differing symbols choose their orientation by the slot's coordinate bit;
//! equal symbols use that bit to select a copy from the padded class.

use crate::Error;
/// Edge identity retained while assembling packet slots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BipartiteEdge {
    pub left: usize,
    pub right: usize,
}
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedPacket {
    /// Sorted coordinate pairs (min, max) for the packet, in order 0..a.
    pub unordered_pairs: Vec<(usize, usize)>,
    /// One source edge index per occupied slot, identical on row and column.
    pub slots: Vec<Option<usize>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PacketLayout {
    pub r: usize,
    pub a: u32,
    pub slots_per_packet: usize,
    pub padded_class_load: usize,
    pub packets: Vec<PackedPacket>,
    /// For every active coordinate, rows/columns with a given symbol.
    pub row_ports: Vec<Vec<usize>>,
    pub column_ports: Vec<Vec<usize>>,
    /// For each coordinate and symbol, source bounds these by 6M/r.
    pub child_edge_upper_counts: Vec<Vec<usize>>,
}

fn cap() -> Error {
    Error::Capacity("bounded packet layout exceeded graph/label limits".into())
}

fn digits(mut number: usize, base: usize, positions: usize) -> Vec<usize> {
    let mut result = Vec::with_capacity(positions);
    for _ in 0..positions {
        result.push(number % base);
        number /= base;
    }
    result
}

/// Pack one small, explicitly labelled bipartite multigraph.
///
/// `degree_cap` must bound the original graph degrees and new packet
/// degrees `2L`; neither is inferred from the appendix's asymptotic
/// Delta. This does not check the source's u schedule or counting semantics.
pub fn pack_bounded(
    edges: &[BipartiteEdge],
    left_labels: &[usize],
    right_labels: &[usize],
    r: usize,
    a: u32,
    degree_cap: usize,
) -> Result<PacketLayout, Error> {
    if edges.is_empty() || r < 2 || a == 0 || a > 3 {
        return Err(Error::Invalid(
            "nonempty graph, r>=2, 1<=a<=3 required".into(),
        ));
    }
    let b = r.checked_pow(a).ok_or_else(cap)?;
    let l = 1usize.checked_shl(a).ok_or_else(cap)?;
    let d = b.checked_mul(b).ok_or_else(cap)?;
    if b > 8 || edges.len() > 32 || left_labels.len() > 32 || right_labels.len() > 32 {
        return Err(cap());
    }
    if left_labels
        .iter()
        .chain(right_labels)
        .any(|&label| label >= b)
    {
        return Err(Error::Invalid(
            "vertex label outside symbol alphabet".into(),
        ));
    }
    if degree_cap < l.checked_mul(2).ok_or_else(cap)? {
        return Err(Error::Invalid(
            "packet vertex degree exceeds supplied cap".into(),
        ));
    }

    let n_coords = usize::try_from(a).map_err(|_| cap())?;
    let mut rows = vec![0usize; left_labels.len()];
    let mut cols = vec![0usize; right_labels.len()];
    let mut classes = vec![Vec::<Option<usize>>::new(); d];
    let mut row_ports = vec![vec![0usize; r]; n_coords];
    let mut column_ports = vec![vec![0usize; r]; n_coords];
    for (index, edge) in edges.iter().enumerate() {
        if edge.left >= rows.len() || edge.right >= cols.len() {
            return Err(Error::Invalid(
                "edge endpoint outside declared vertex part".into(),
            ));
        }
        rows[edge.left] += 1;
        cols[edge.right] += 1;
        let row = left_labels[edge.left];
        let col = right_labels[edge.right];
        classes[row * b + col].push(Some(index));
        let rd = digits(row, r, n_coords);
        let cd = digits(col, r, n_coords);
        for i in 0..n_coords {
            row_ports[i][rd[i]] += 1;
            column_ports[i][cd[i]] += 1;
        }
    }
    if rows.iter().chain(&cols).any(|&degree| degree > degree_cap) {
        return Err(Error::Invalid(
            "original graph degree exceeds supplied cap".into(),
        ));
    }
    let m = edges.len();
    let maximum = classes.iter().map(Vec::len).max().unwrap_or(0);
    let hpad = maximum.div_ceil(l).checked_mul(l).ok_or_else(cap)?;
    if hpad.checked_mul(d).ok_or_else(cap)? > m.checked_mul(3).ok_or_else(cap)? {
        return Err(Error::Capacity(
            "actual padded label-class loads exceed 3M/D".into(),
        ));
    }
    let mut child_edge_upper_counts = vec![vec![0usize; r]; n_coords];
    for i in 0..n_coords {
        for symbol in 0..r {
            let row_count = row_ports[i][symbol];
            let column_count = column_ports[i][symbol];
            if row_count.checked_mul(r).ok_or_else(cap)? > m.checked_mul(3).ok_or_else(cap)?
                || column_count.checked_mul(r).ok_or_else(cap)?
                    > m.checked_mul(3).ok_or_else(cap)?
            {
                return Err(Error::Invalid("coordinate symbol port cap exceeded".into()));
            }
            child_edge_upper_counts[i][symbol] = row_count + column_count;
        }
    }
    for class in &mut classes {
        class.resize(hpad, None);
    }

    // Every tuple of unordered per-coordinate symbol pairs occurs, and
    // the ordered classes under it differ only by orientations.
    let mut groups = BTreeMap::<Vec<(usize, usize)>, Vec<usize>>::new();
    for row in 0..b {
        for col in 0..b {
            let rd = digits(row, r, n_coords);
            let cd = digits(col, r, n_coords);
            let signature = rd
                .iter()
                .zip(&cd)
                .map(|(&x, &y)| (x.min(y), x.max(y)))
                .collect::<Vec<_>>();
            groups.entry(signature).or_default().push(row * b + col);
        }
    }
    let mut packets = Vec::new();
    for (signature, ordered_classes) in groups {
        let equal_coordinates = signature.iter().filter(|(x, y)| x == y).count();
        let unequal_coordinates = n_coords - equal_coordinates;
        let copies = 1usize << equal_coordinates;
        if ordered_classes.len() != 1usize << unequal_coordinates || !hpad.is_multiple_of(copies) {
            return Err(Error::Invalid(
                "unordered symbol-pair class multiplicity invalid".into(),
            ));
        }
        for chunk in 0..(hpad / copies) {
            let mut slots = Vec::with_capacity(l);
            for slot in 0..l {
                let mut row_label = 0usize;
                let mut col_label = 0usize;
                let mut base_power = 1usize;
                let mut copy_index = 0usize;
                let mut copy_power = 1usize;
                for (i, &(lo, hi)) in signature.iter().enumerate() {
                    let bit = (slot >> i) & 1;
                    let (row_symbol, col_symbol) = if lo == hi {
                        copy_index += bit * copy_power;
                        copy_power *= 2;
                        (lo, hi)
                    } else if bit == 0 {
                        (lo, hi)
                    } else {
                        (hi, lo)
                    };
                    row_label += row_symbol * base_power;
                    col_label += col_symbol * base_power;
                    base_power *= r;
                }
                let class = row_label * b + col_label;
                let source_index = chunk * copies + copy_index;
                slots.push(classes[class][source_index]);
            }
            packets.push(PackedPacket {
                unordered_pairs: signature.clone(),
                slots,
            });
        }
    }

    let expected_packets = hpad.checked_mul(d).ok_or_else(cap)? / l;
    if packets.len() != expected_packets
        || packets.len().checked_mul(l).ok_or_else(cap)? != hpad.checked_mul(d).ok_or_else(cap)?
    {
        return Err(Error::Invalid(
            "packet decomposition lost padded slots".into(),
        ));
    }
    let mut seen = vec![false; m];
    for packet in &packets {
        for (slot, maybe_edge) in packet.slots.iter().enumerate() {
            if let Some(index) = maybe_edge {
                if *index >= m || seen[*index] {
                    return Err(Error::Invalid("source edge appears more than once".into()));
                }
                seen[*index] = true;
                let edge = edges[*index];
                let rd = digits(left_labels[edge.left], r, n_coords);
                let cd = digits(right_labels[edge.right], r, n_coords);
                for i in 0..n_coords {
                    let (lo, hi) = packet.unordered_pairs[i];
                    if (rd[i].min(cd[i]), rd[i].max(cd[i])) != (lo, hi) {
                        return Err(Error::Invalid("packet pair orientation mismatch".into()));
                    }
                    if lo != hi {
                        let bit = (slot >> i) & 1;
                        let expected = if bit == 0 { (lo, hi) } else { (hi, lo) };
                        if (rd[i], cd[i]) != expected {
                            return Err(Error::Invalid("slot bit orientation mismatch".into()));
                        }
                    }
                }
            }
        }
    }
    if seen.contains(&false) {
        return Err(Error::Invalid("packet layout omitted a real edge".into()));
    }
    Ok(PacketLayout {
        r,
        a,
        slots_per_packet: l,
        padded_class_load: hpad,
        packets,
        row_ports,
        column_ports,
        child_edge_upper_counts,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::matching_packing::{BipartiteGraph, construct_matching_labels};

    #[test]
    fn constructed_matching_labels_pack_all_edges_with_original_slots() {
        // Abstract a=1 packet example, not the fixed source u>=1 schedule.
        let edges = (0..16)
            .map(|i| BipartiteEdge { left: i, right: i })
            .collect::<Vec<_>>();
        let graph = BipartiteGraph {
            left_vertices: 16,
            right_vertices: 16,
            edges: edges.iter().map(|e| (e.left, e.right)).collect(),
        };
        let labels = construct_matching_labels(&graph, 2).unwrap();
        let left = labels.left_labels.iter().map(|&x| x as usize).collect::<Vec<_>>();
        let right = labels.right_labels.iter().map(|&x| x as usize).collect::<Vec<_>>();
        let layout = pack_bounded(&edges, &left, &right, 2, 1, 4).unwrap();
        assert_eq!(layout.slots_per_packet, 2);
        assert!(layout.packets.len() <= 3 * edges.len() / 2);
        assert_eq!(
            layout
                .packets
                .iter()
                .flat_map(|packet| packet.slots.iter())
                .filter(|slot| slot.is_some())
                .count(),
            edges.len()
        );
        for coordinate in &layout.child_edge_upper_counts {
            for &edges_for_group in coordinate {
                assert!(edges_for_group * layout.r <= 6 * edges.len());
            }
        }
    }

    #[test]
    fn two_coordinate_orientations_and_equal_copies_are_exact() {
        // r=2,a=2: all 16 ordered classes each hold two parallel edges.
        // Degrees are 8 and packet vertex degrees are <=2L=8.
        let mut edges = Vec::new();
        for row in 0..4 {
            for col in 0..4 {
                for _ in 0..2 {
                    edges.push(BipartiteEdge {
                        left: row,
                        right: col,
                    });
                }
            }
        }
        let labels = [0, 1, 2, 3];
        let layout = pack_bounded(&edges, &labels, &labels, 2, 2, 8).unwrap();
        assert_eq!(layout.padded_class_load, 4);
        assert_eq!(layout.slots_per_packet, 4);
        assert_eq!(layout.packets.len(), 16);
        assert_eq!(
            layout
                .packets
                .iter()
                .flat_map(|packet| packet.slots.iter())
                .flatten()
                .count(),
            32
        );
    }

    #[test]
    fn refuse_actual_overload_invalid_labels_and_degrees() {
        let repeated = vec![BipartiteEdge { left: 0, right: 0 }; 16];
        assert!(pack_bounded(&repeated, &[0], &[0], 2, 1, 16).is_err());
        let small = [BipartiteEdge { left: 0, right: 0 }];
        assert!(pack_bounded(&small, &[2], &[0], 2, 1, 4).is_err());
        assert!(pack_bounded(&small, &[0], &[0], 2, 1, 1).is_err());
        assert!(pack_bounded(&small, &[0], &[0], 2, 1, 4).is_err());
    }
}
