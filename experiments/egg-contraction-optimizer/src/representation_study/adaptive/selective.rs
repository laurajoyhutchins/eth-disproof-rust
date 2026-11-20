//! Conditional tropical lookahead for ambiguous min-fill factor admissions.
//!
//! The gate is entirely structural and fixed before examining these runs:
//! only the first two candidates with identical (fill edges, kept-cell count)
//! are eligible. Each preview union must have <= 64 assignments, and the
//! *entire run* has <= 1,024 tropical multiplication slots, including replay.
//!
//! We deliberately rebuild the current shadow from the selected prefix only
//! when the gate opens. Rebuilding, rejected candidates, source leaf evaluations
//! and all future attempts are charged to the planner. Without an ambiguity,
//! this policy builds no tropical tables at all.

use super::*;

const SHORTLIST: usize = 2;
const MAX_UNION_CELLS: usize = 64;
const MAX_TOTAL_TROPICAL_MULTIPLICATIONS: u64 = 1_024;

#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub ambiguity_steps: usize,
    pub purchases: usize,
    pub budget_skips: usize,
    pub changed_choices: usize,
    pub candidates_previewed: usize,
    pub replay_merges: usize,
    pub source_leaf_cells_built: usize,
}

#[derive(Clone, Debug)]
struct StructuralChoice {
    factor: usize,
    kept: Vec<String>,
    /// A stable, source-only rank; the last component breaks exact ties.
    score: (usize, usize, usize, usize),
}

fn future_ports(
    remaining: &BTreeSet<usize>, skip: usize, scopes: &[Vec<String>],
) -> BTreeSet<String> {
    remaining.iter().filter(|&&idx| idx != skip)
        .flat_map(|&idx| scopes[idx].iter().cloned()).collect()
}

fn choice(
    active: &[String], remaining: &BTreeSet<usize>,
    scopes: &[Vec<String>], index: usize,
) -> Result<StructuralChoice, String> {
    let active_set = active.iter().cloned().collect::<BTreeSet<_>>();
    let candidate_set = scopes[index].iter().cloned().collect::<BTreeSet<_>>();
    let kept = affine_orders::kept_port_set(
        &active_set, &candidate_set,
        &future_ports(remaining, index, scopes), &BTreeSet::new(),
    ).into_iter().collect::<Vec<_>>();
    let union = union_ports(active, &scopes[index]);
    let score = (
        fill_edges(active, remaining, scopes, &kept, index),
        count_masks(kept.len())?,
        count_masks(union.len())?,
        index,
    );
    Ok(StructuralChoice { factor: index, kept, score })
}

/// Cost of reconstructing the *same* liveness-constrained prefix. This is
/// decided without evaluating any source predicate or tropical data.
fn prefix_replay_merges(
    prefix: &[usize], scopes: &[Vec<String>],
) -> Result<(usize, Vec<String>), String> {
    let mut absorbed = BTreeSet::from([prefix[0]]);
    let mut ports = scopes[prefix[0]].clone();
    let mut cost = 0usize;
    for &index in &prefix[1..] {
        let remaining = (0..scopes.len()).filter(|j| !absorbed.contains(j))
            .collect::<BTreeSet<_>>();
        let candidate = choice(&ports, &remaining, scopes, index)?;
        cost = cost.checked_add(candidate.score.2)
            .ok_or("tropical prefix replay work overflow")?;
        ports = candidate.kept;
        absorbed.insert(index);
    }
    Ok((cost, ports))
}

fn build_leaf(factors: &[Factor], index: usize, stats: &mut Stats)
    -> Result<TropicalStage, String>
{
    stats.source_leaf_cells_built = stats.source_leaf_cells_built
        .checked_add(count_masks(factors[index].ports.len())?)
        .ok_or("tropical leaf accounting overflow")?;
    TropicalStage::from_factor(&factors[index])
}

/// The selected partial factor fold can be reconstituted from the same
/// source factors, port sets and schedule. No intervening exact polynomial
/// coefficients are inspected. These merges are fully charged.
fn rebuild_prefix(
    factors: &[Factor], scopes: &[Vec<String>], prefix: &[usize],
    work: &mut Work, stats: &mut Stats,
) -> Result<TropicalStage, String> {
    let mut stage = build_leaf(factors, prefix[0], stats)?;
    let mut absorbed = BTreeSet::from([prefix[0]]);
    for &index in &prefix[1..] {
        let remaining = (0..scopes.len()).filter(|j| !absorbed.contains(j))
            .collect::<BTreeSet<_>>();
        let candidate = choice(&stage.ports, &remaining, scopes, index)?;
        let leaf = build_leaf(factors, index, stats)?;
        stage = stage.merge(&leaf, &candidate.kept, work)?;
        stats.replay_merges += 1;
        absorbed.insert(index);
    }
    Ok(stage)
}

pub(super) fn make_plan(factors: &[Factor]) -> Result<Plan, String> {
    let clock = Instant::now();
    if factors.len() < 2 { return Err("study needs at least two factors".into()); }

    let scopes = factors.iter().map(|f| f.ports.clone()).collect::<Vec<_>>();
    let mut order = vec![0];
    let mut remaining = (1..factors.len()).collect::<BTreeSet<_>>();
    let mut ports = scopes[0].clone();
    let mut work = Work::default();
    let mut candidates_examined = 0usize;
    let mut peak_preview_payload_bytes = 0;
    let mut stats = Stats::default();

    while !remaining.is_empty() {
        let mut ranked = remaining.iter().map(|&index| {
            choice(&ports, &remaining, &scopes, index)
        }).collect::<Result<Vec<_>, _>>()?;
        candidates_examined += ranked.len();
        ranked.sort_by_key(|candidate| candidate.score);
        let default = &ranked[0];
        let mut selected = default.factor;
        let mut selected_kept = default.kept.clone();

        // Only a structural tie on fill and retained size can buy tropical
        // information. Two top candidates maximum, regardless of tie count.
        let ambiguous = ranked.get(1).is_some_and(|second|
            second.score.0 == default.score.0
                && second.score.1 == default.score.1);
        if ambiguous {
            stats.ambiguity_steps += 1;
            let shortlist = &ranked[..SHORTLIST];
            let (replay_cells, expected_ports) =
                prefix_replay_merges(&order, &scopes)?;
            if expected_ports != ports {
                return Err("prefix liveness reconstruction disagrees with plan".into());
            }
            let next_cells = shortlist.iter().try_fold(0usize, |sum, c| {
                sum.checked_add(c.score.2).ok_or("preview work overflow")
            })?;
            let budget_required = replay_cells.checked_add(next_cells)
                .ok_or("replay-plus-preview work overflow")?;
            let small_enough = shortlist.iter().all(|c| c.score.2 <= MAX_UNION_CELLS);
            let within_budget = budget_required as u64
                <= MAX_TOTAL_TROPICAL_MULTIPLICATIONS
                    .saturating_sub(work.multiplications);
            if small_enough && within_budget {
                let current = rebuild_prefix(
                    factors, &scopes, &order, &mut work, &mut stats,
                )?;
                if current.ports != ports {
                    return Err("tropical prefix ports differ from structural prefix".into());
                }
                let mut best: Option<(u128, u128, u64, usize)> = None;
                for candidate in shortlist {
                    let leaf = build_leaf(factors, candidate.factor, &mut stats)?;
                    let mut preview_work = Work::default();
                    let preview = current.merge(&leaf, &candidate.kept, &mut preview_work)?;
                    peak_preview_payload_bytes = peak_preview_payload_bytes.max(
                        current.bit_payload_bytes()
                            + leaf.bit_payload_bytes()
                            + preview.bit_payload_bytes());
                    stats.candidates_previewed += 1;
                    add_work(&mut work, &preview_work);
                    let score = (
                        (candidate.score.1 as u128) +
                            4 * (preview.zero_energy_cells() as u128),
                        candidate.score.2 as u128,
                        preview_work.multiplications,
                        candidate.factor,
                    );
                    if best.is_none_or(|old| score < old) {
                        best = Some(score);
                        selected = candidate.factor;
                        selected_kept = candidate.kept.clone();
                    }
                }
                stats.purchases += 1;
                if selected != default.factor { stats.changed_choices += 1; }
                if work.multiplications > MAX_TOTAL_TROPICAL_MULTIPLICATIONS {
                    return Err("purchased more tropical work than budget".into());
                }
            } else {
                stats.budget_skips += 1;
            }
        }

        // Even a rejected tropical score never affects exact semantics:
        // the chosen index still occurs once, and exact execution later uses
        // exactly the same live-set rule as every other policy.
        if !remaining.remove(&selected) {
            return Err("selective planner selected a consumed factor".into());
        }
        order.push(selected);
        ports = selected_kept;
    }

    Ok(Plan {
        order, work, candidates_examined,
        planned_ns: clock.elapsed().as_nanos(),
        peak_preview_payload_bytes,
        selective_stats: Some(stats),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_ambiguity_never_purchases_tropical_data() {
        // A single future factor cannot produce an ambiguous choice.
        let factors = generate(StudyFamily::EqualityChain, 3).unwrap();
        let plan = make_plan(&factors).unwrap();
        let stats = plan.selective_stats.unwrap();
        assert!(stats.purchases <= stats.ambiguity_steps);
        assert_eq!(stats.candidates_previewed, 2 * stats.purchases);
        assert!(plan.work.multiplications <= MAX_TOTAL_TROPICAL_MULTIPLICATIONS);
    }

    #[test]
    fn replay_matches_exact_stage_tropical_values_for_every_prefix() {
        let case = Case {
            kind: CaseKind::Random3Cnf, variables: 6,
            clauses: 12, seed: 1009,
        };
        let factors = source_case(case).unwrap();
        let scopes = factors.iter().map(|f| f.ports.clone()).collect::<Vec<_>>();
        let structural = super::make_plan(&factors, Policy::MinFillAdmission).unwrap();
        let leaves = factors.iter().map(Tables::from_factor)
            .collect::<Result<Vec<_>, _>>().unwrap();
        let mut exact = leaves[structural.order[0]].clone();
        for step in 1..structural.order.len() {
            let prefix = &structural.order[..=step];
            let mut work = Work::default();
            let mut stats = Stats::default();
            let replay = rebuild_prefix(&factors, &scopes, prefix, &mut work, &mut stats)
                .unwrap();
            let index = structural.order[step];
            let future = structural.order[step+1..].iter()
                .flat_map(|&j| leaves[j].ports.iter().cloned())
                .collect::<BTreeSet<_>>();
            let kept = affine_orders::kept_port_set(
                &exact.ports.iter().cloned().collect(),
                &leaves[index].ports.iter().cloned().collect(),
                &future, &BTreeSet::new(),
            ).into_iter().collect::<Vec<_>>();
            exact = exact.merge(
                &leaves[index], &kept, &mut Work::default(), &mut Work::default(),
            ).unwrap();
            assert_eq!(replay.ports, exact.ports);
            assert_eq!(replay.values, exact.tropical);
        }
    }
}
