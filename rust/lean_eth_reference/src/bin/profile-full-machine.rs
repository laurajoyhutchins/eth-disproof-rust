//! Observational native Rust BitProgram profiler for the imported-Lean
//! full-machine differential. No instruction or state semantics are changed.
//! Timings include instrumentation overhead and are NOT TM2 primitive costs.
use lean_eth_reference::bit_program::{Instr, Program};
use lean_eth_reference::native_high::branch_program;
use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_answer;
use lean_eth_reference::native_frontend;
use lean_eth_reference::native_terminal_classifier;
use lean_eth_reference::native_terminal_count::{count_terminal, count_to_answer_input_program};
use lean_eth_reference::Cnf;

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::Instant;

static MEASURE: AtomicBool = AtomicBool::new(false);
static ALLOCS: AtomicU64 = AtomicU64::new(0);
static REALLOCS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);
struct CountAlloc;
#[global_allocator]
static GLOBAL: CountAlloc = CountAlloc;

// SAFETY: every allocation operation is passed through unchanged to System.
// Atomic counters are passive, and no heap allocation is used in recording.
unsafe impl GlobalAlloc for CountAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if MEASURE.load(Ordering::Relaxed) {
            ALLOCS.fetch_add(1, Ordering::Relaxed);
            BYTES.fetch_add(
                u64::try_from(layout.size()).unwrap_or(u64::MAX),
                Ordering::Relaxed,
            );
        }
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if MEASURE.load(Ordering::Relaxed) {
            ALLOCS.fetch_add(1, Ordering::Relaxed);
            BYTES.fetch_add(
                u64::try_from(layout.size()).unwrap_or(u64::MAX),
                Ordering::Relaxed,
            );
        }
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if MEASURE.load(Ordering::Relaxed) {
            REALLOCS.fetch_add(1, Ordering::Relaxed);
            BYTES.fetch_add(
                u64::try_from(new_size).unwrap_or(u64::MAX),
                Ordering::Relaxed,
            );
        }
        unsafe { System.realloc(ptr, layout, new_size) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

const OPCODES: [&str; 12] = [
    "halt", "goto", "set", "copy", "not", "and", "or", "xor", "branch", "push", "peek", "pop",
];
fn opcode(op: &Instr) -> usize {
    match op {
        Instr::Halt => 0,
        Instr::Goto { .. } => 1,
        Instr::Set { .. } => 2,
        Instr::Copy { .. } => 3,
        Instr::Not { .. } => 4,
        Instr::And { .. } => 5,
        Instr::Or { .. } => 6,
        Instr::Xor { .. } => 7,
        Instr::Branch { .. } => 8,
        Instr::Push { .. } => 9,
        Instr::Peek { .. } => 10,
        Instr::Pop { .. } => 11,
    }
}
#[derive(Clone, Copy, Default)]
struct Measure {
    transitions: u64,
    elapsed_ns: u128,
    allocations: u64,
    reallocations: u64,
    bytes_requested: u64,
}
fn run_case(
    program: &Program<2, 2>,
    name: &str,
    size: usize,
    code: usize,
    dirty: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let input = (0..size).map(|i| ((code >> i) & 1) != 0);
    let mut cfg = program.initial(input);
    if dirty {
        cfg.regs = [true, true];
        cfg.stacks[1].extend([true, false]);
    }
    let mut metrics = [Measure::default(); 12];
    let mut peak_bits = cfg.stack_bits()?;
    let mut peak_capacity: usize = cfg
        .stacks
        .iter()
        .map(std::collections::VecDeque::capacity)
        .sum();
    for _ in 0..512 {
        let Some(pc) = cfg.pc else { break };
        let op = opcode(&program.code()[pc]);
        let alloc_before = ALLOCS.load(Ordering::Relaxed);
        let realloc_before = REALLOCS.load(Ordering::Relaxed);
        let bytes_before = BYTES.load(Ordering::Relaxed);
        let start = Instant::now();
        MEASURE.store(true, Ordering::Relaxed);
        let result = program.step(&mut cfg);
        MEASURE.store(false, Ordering::Relaxed);
        let duration = start.elapsed().as_nanos();
        result?;
        let item = &mut metrics[op];
        item.transitions += 1;
        item.elapsed_ns += duration;
        item.allocations += ALLOCS.load(Ordering::Relaxed) - alloc_before;
        item.reallocations += REALLOCS.load(Ordering::Relaxed) - realloc_before;
        item.bytes_requested += BYTES.load(Ordering::Relaxed) - bytes_before;
        peak_bits = peak_bits.max(cfg.stack_bits()?);
        peak_capacity = peak_capacity.max(
            cfg.stacks
                .iter()
                .map(std::collections::VecDeque::capacity)
                .sum(),
        );
    }
    if cfg.pc.is_some() {
        return Err(format!("source-instruction fuel exhausted: {name}").into());
    }
    for (index, metric) in metrics.iter().enumerate() {
        if metric.transitions == 0 {
            continue;
        }
        println!(
            "{name},{},{},{},{},{},{},{},{},{}",
            OPCODES[index],
            metric.transitions,
            metric.elapsed_ns,
            metric.allocations,
            metric.reallocations,
            metric.bytes_requested,
            peak_bits,
            peak_capacity,
            "NA",
        );
    }
    Ok(())
}
/// Cost of the *real* four-stage bounded terminal path, split by stage and
/// opcode. Unlike the smaller branch-program observer this uses the production
/// physical 80-register/1220-stack instruction tables without a host SAT step.
fn profile_terminal_stage(
    p: &Program<80, 1220>,
    state: &mut Config<80, 1220>,
    case: &str,
    cap: u64,
) -> Result<u64, Box<dyn std::error::Error>> {
    state.pc = Some(p.entry());
    let mut measures = [Measure::default(); 12];
    let mut peak_bits = state.stack_bits()?;
    let mut live_bits = peak_bits;
    let mut capacity = state.stacks.iter().map(std::collections::VecDeque::capacity).sum::<usize>();
    let mut peak_capacity = capacity;

    let mut steps = 0;
    while let Some(pc) = state.pc {
        if steps >= cap {
            return Err(format!("source stage {case} exhausted its {cap} instructions").into());
        }
        let instr = &p.code()[pc];
        let op = opcode(instr);
        let touched = match instr {
            Instr::Push { stack, .. } | Instr::Pop { stack, .. } => Some(*stack),
            _ => None,
        };
        let old_capacity = touched.map(|s| state.stacks[s].capacity()).unwrap_or(0);
        let delta = match instr {
            Instr::Push { .. } => 1_i8,
            Instr::Pop { stack, .. } if !state.stacks[*stack].is_empty() => -1_i8,
            _ => 0_i8,
        };
        let a = ALLOCS.load(Ordering::Relaxed);
        let r = REALLOCS.load(Ordering::Relaxed);
        let b = BYTES.load(Ordering::Relaxed);
        let start = Instant::now();
        MEASURE.store(true, Ordering::Relaxed);
        let result = p.step(state);
        MEASURE.store(false, Ordering::Relaxed);
        let elapsed = start.elapsed().as_nanos();
        result?;

        let measure = &mut measures[op];
        measure.transitions += 1;
        measure.elapsed_ns += elapsed;
        measure.allocations += ALLOCS.load(Ordering::Relaxed) - a;
        measure.reallocations += REALLOCS.load(Ordering::Relaxed) - r;
        measure.bytes_requested += BYTES.load(Ordering::Relaxed) - b;
        if delta > 0 {
            live_bits += 1;
        } else if delta < 0 {
            live_bits -= 1;
        }
        peak_bits = peak_bits.max(live_bits);
        if let Some(s) = touched {
            let next = state.stacks[s].capacity();
            capacity = capacity - old_capacity + next;
            peak_capacity = peak_capacity.max(capacity);
        }
        steps += 1;
    }
    if live_bits != state.stack_bits()? {
        return Err(format!("{case}: incremental live-stack accounting diverged").into());
    }
    for (index, measure) in measures.iter().enumerate() {
        if measure.transitions == 0 {
            continue;
        }
        println!(
            "{case},{},{},{},{},{},{},{},{},NA",
            OPCODES[index],
            measure.transitions,
            measure.elapsed_ns,
            measure.allocations,
            measure.reallocations,
            measure.bytes_requested,
            peak_bits,
            peak_capacity,
        );
    }
    Ok(steps)
}

/// The terminal test cases have complete source-produced counts and are
/// independently re-run through the normal, uninstrumented production path.
/// This does not replace the missing full source-Lean terminal differential.
fn profile_terminal_cases() -> Result<(), Box<dyn std::error::Error>> {
    let stages: [(&str, Program<80, 1220>); 4] = [
        ("frontend", native_frontend::program()?),
        ("terminal", native_terminal_classifier::ready_program()?),
        ("transfer_adapter", count_to_answer_input_program()?),
        ("answer", native_answer::answer_program()?),
    ];
    let cases = [
        ("zero_empty", Cnf::from_signed(0, &[])?),
        ("three_empty", Cnf::from_signed(3, &[])?),
        ("three_empty_clause", Cnf::from_signed(3, &[&[]])?),
        ("two_tautology", Cnf::from_signed(2, &[&[-1, 1]])?),
    ];
    let limits = RunLimits { max_steps: 20_000_000, max_stack_bits: 300_000 };
    for (name, cnf) in cases {
        let unobserved = count_terminal(&cnf, limits)?;
        let frontend = &stages[0].1;
        let mut state = frontend.initial(cnf.encode_lean().bytes().map(|x| x == b'1'));
        let mut n = 0;
        for (i, (stage, program)) in stages.iter().enumerate() {
            let before = n;
            n += profile_terminal_stage(program, &mut state, &format!("{name}_{stage}"), limits.max_steps - n)?;
            if n - before != unobserved.stages[i].instructions {
                return Err(format!("{name}/{stage}: instrumented and ordinary stage instruction counts disagree").into());
            }
        }
        if n != unobserved.total_instructions {
            return Err(format!("{name}: cumulative step count disagrees").into());
        }
        if state.stacks[263].iter().copied().collect::<Vec<_>>() != unobserved.count_lsb {
            return Err(format!("{name}: source count word disagrees after instrumented trace").into());
        }
        if state.stacks[1216].front().copied() != Some(unobserved.positive) {
            return Err(format!("{name}: source answer disagrees after instrumented trace").into());
        }
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let terminal = match std::env::args().skip(1).collect::<Vec<_>>().as_slice() {
        [] => false,
        [flag] if flag == "--terminal" => true,
        _ => return Err("usage: profile-full-machine [--terminal]".into()),
    };
    if terminal {
        println!("case,opcode,transitions,elapsed_ns,allocation_calls,reallocation_calls,requested_bytes,peak_stack_bits,peak_stack_capacity_bits,max_integer_bits");
        return profile_terminal_cases();
    }
    let p = branch_program()?;
    // No commas occur in the case names. These are physical source-op counts,
    // Rust heap allocation events inside step(), and stack capacity, NOT TM2.
    println!(
        "case,opcode,transitions,elapsed_ns,allocation_calls,reallocation_calls,requested_bytes,peak_stack_bits,peak_stack_capacity_bits,max_integer_bits"
    );
    for size in 0..=4_usize {
        for code in 0..(1_usize << size) {
            for dirty in [false, true] {
                let name = format!("{size}_{code}_{}", if dirty { "dirty" } else { "clean" });
                run_case(&p, &name, size, code, dirty)?;
            }
        }
    }
    Ok(())
}
