//! Observational native Rust BitProgram profiler for the imported-Lean
//! full-machine differential. No instruction or state semantics are changed.
//! Timings include instrumentation overhead and are NOT TM2 primitive costs.
use lean_eth_reference::bit_program::{Instr, Program};
use lean_eth_reference::native_high::branch_program;
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
            BYTES.fetch_add(u64::try_from(layout.size()).unwrap_or(u64::MAX), Ordering::Relaxed);
        }
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if MEASURE.load(Ordering::Relaxed) {
            ALLOCS.fetch_add(1, Ordering::Relaxed);
            BYTES.fetch_add(u64::try_from(layout.size()).unwrap_or(u64::MAX), Ordering::Relaxed);
        }
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if MEASURE.load(Ordering::Relaxed) {
            REALLOCS.fetch_add(1, Ordering::Relaxed);
            BYTES.fetch_add(u64::try_from(new_size).unwrap_or(u64::MAX), Ordering::Relaxed);
        }
        unsafe { System.realloc(ptr, layout, new_size) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

const OPCODES: [&str; 12] = [
    "halt", "goto", "set", "copy", "not", "and", "or", "xor",
    "branch", "push", "peek", "pop",
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
    let mut peak_capacity: usize = cfg.stacks.iter().map(std::collections::VecDeque::capacity).sum();
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
        peak_capacity = peak_capacity.max(cfg.stacks.iter().map(std::collections::VecDeque::capacity).sum());
    }
    if cfg.pc.is_some() {
        return Err(format!("source-instruction fuel exhausted: {name}").into());
    }
    for (index, metric) in metrics.iter().enumerate() {
        if metric.transitions == 0 { continue }
        println!(
            "{name},{},{},{},{},{},{},{},{}",
            OPCODES[index], metric.transitions, metric.elapsed_ns,
            metric.allocations, metric.reallocations, metric.bytes_requested,
            peak_bits, peak_capacity, "NA",
        );
    }
    Ok(())
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let p = branch_program()?;
    // No commas occur in the case names. These are physical source-op counts,
    // Rust heap allocation events inside step(), and stack capacity, NOT TM2.
    println!("case,opcode,transitions,elapsed_ns,allocation_calls,reallocation_calls,requested_bytes,peak_stack_bits,peak_stack_capacity_bits,max_integer_bits");
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
