use crate::{arith::{Node, Plan, Polynomial}, Arithmetic};
use egg::{rewrite as rw, EGraph, Id, Language, RecExpr, Rewrite, Runner};
use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

fn rules() -> Vec<Rewrite<Arithmetic, ()>> {
    vec![
        rw!("associate-add-left"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("associate-add-right"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("factor-left"; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        rw!("distribute-left"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("add-zero"; "(+ ?a 0)" => "?a"),
        rw!("mul-one"; "(* ?a 1)" => "?a"),
        rw!("mul-zero"; "(* ?a 0)" => "0"),
    ]
}

impl Plan {
    fn from_selection(
        egraph: &EGraph<Arithmetic, ()>,
        root: Id,
        chosen: &HashMap<Id, Arithmetic>,
    ) -> Result<Self, String> {
        fn visit(
            id: Id,
            eg: &EGraph<Arithmetic, ()>,
            chosen: &HashMap<Id, Arithmetic>,
            active: &mut HashSet<Id>,
            finished: &mut HashMap<Id, usize>,
            nodes: &mut Vec<Node>,
        ) -> Result<usize, String> {
            let id = eg.find(id);
            if let Some(&index) = finished.get(&id) { return Ok(index); }
            if !active.insert(id) { return Err("cyclic e-class selection refused".into()); }
            let enode = chosen.get(&id).ok_or("missing selected e-class")?;
            let new_node = match enode {
                Arithmetic::Number(n) => Node::Number(*n),
                Arithmetic::Variable(s) => Node::Variable(s.to_string()),
                Arithmetic::Add([a, b]) => Node::Add(
                    visit(*a, eg, chosen, active, finished, nodes)?,
                    visit(*b, eg, chosen, active, finished, nodes)?,
                ),
                Arithmetic::Mul([a, b]) => Node::Mul(
                    visit(*a, eg, chosen, active, finished, nodes)?,
                    visit(*b, eg, chosen, active, finished, nodes)?,
                ),
                Arithmetic::Pair([a, b]) => Node::Pair(
                    visit(*a, eg, chosen, active, finished, nodes)?,
                    visit(*b, eg, chosen, active, finished, nodes)?,
                ),
            };
            active.remove(&id);
            let index = nodes.len();
            nodes.push(new_node);
            finished.insert(id, index);
            Ok(index)
        }
        let mut nodes = Vec::new();
        let root = visit(
            root, egraph, chosen,
            &mut HashSet::new(), &mut HashMap::new(), &mut nodes,
        )?;
        let outputs = match nodes[root] {
            Node::Pair(a, b) => [a, b],
            _ => return Err("expected an extracted pair root".into()),
        };
        Ok(Self { nodes, outputs })
    }
}

fn first_unassigned(
    egraph: &EGraph<Arithmetic, ()>,
    root: Id,
    selected: &HashMap<Id, Arithmetic>,
) -> Option<Id> {
    let mut stack = vec![root];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        let id = egraph.find(id);
        if !seen.insert(id) { continue; }
        if let Some(enode) = selected.get(&id) {
            stack.extend(enode.children().iter().copied());
        } else {
            return Some(id);
        }
    }
    None
}

struct Search<'a> {
    egraph: &'a EGraph<Arithmetic, ()>,
    root: Id,
    target: [Polynomial; 2],
    best: Plan,
    budget: usize,
    states: usize,
    complete: bool,
    refused: usize,
}

impl Search<'_> {
    fn explore(&mut self, chosen: &mut HashMap<Id, Arithmetic>) {
        if self.states >= self.budget {
            self.complete = false;
            return;
        }
        self.states += 1;
        if let Some(id) = first_unassigned(self.egraph, self.root, chosen) {
            // Clone before recursion so selection does not borrow self immutably.
            let alternatives = self.egraph[id].nodes.clone();
            for node in alternatives {
                chosen.insert(id, node);
                self.explore(chosen);
                chosen.remove(&id);
                if !self.complete { break; }
            }
        } else if let Ok(candidate) = Plan::from_selection(self.egraph, self.root, chosen) {
            if candidate.operation_count() < self.best.operation_count() {
                match candidate.polynomials() {
                    Ok(p) if p == self.target => self.best = candidate,
                    _ => self.refused += 1,
                }
            }
        }
    }
}

/// When complete, optimal only among *single-representative-per-e-class*
/// choices in this finite e-graph under the operation-count cost function.
/// Incomplete saturation or a search budget never becomes an optimality claim.
#[derive(Debug)]
pub struct Report {
    pub baseline: Plan,
    pub optimized: Plan,
    pub search_states: usize,
    pub complete: bool,
    pub refused_candidates: usize,
    pub eclasses: usize,
    pub enodes: usize,
    pub saturation_stop: String,
    pub elapsed: Duration,
}

pub fn optimize(input: &str, budget: usize) -> Result<Report, String> {
    let initial: RecExpr<Arithmetic> = input.parse().map_err(|e| format!("parse: {e}"))?;
    let baseline = Plan::from_expr(&initial)?;
    let target = baseline.polynomials()?; // No oracle, no optimization.
    let started = Instant::now();
    let runner = Runner::<Arithmetic, ()>::default()
        .with_expr(&initial)
        .with_iter_limit(5)
        .with_node_limit(2_000)
        .with_time_limit(Duration::from_secs(2))
        .run(&rules());
    let saturation_stop = format!("{:?}", runner.stop_reason);
    let eclasses = runner.egraph.classes().count();
    let enodes = runner.egraph.classes().map(|c| c.nodes.len()).sum();
    let mut search = Search {
        egraph: &runner.egraph,
        root: runner.roots[0],
        target,
        best: baseline.clone(),
        budget,
        states: 0,
        complete: true,
        refused: 0,
    };
    search.explore(&mut HashMap::new());
    Ok(Report {
        baseline,
        optimized: search.best,
        search_states: search.states,
        complete: search.complete,
        refused_candidates: search.refused,
        eclasses,
        enodes,
        saturation_stop,
        elapsed: started.elapsed(),
    })
}
