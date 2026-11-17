//! Source table decoding is independent of the compiled Rust `Cmd` builder.
//! A hand-written control table exercises the importer but is NOT evidence of
//! an actual Lean query until the pinned Lean exporter runs.
use std::io::Cursor;

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Instr, RunLimits};
use lean_eth_reference::native_query_table::{
    ImportLimits, QUERY_SOURCE_BLOB, SOURCE_COMMIT, import_query_table,
};

fn table(records: &[&str]) -> String {
    let mut out = format!(
        "PIN|query|{SOURCE_COMMIT}|{QUERY_SOURCE_BLOB}\nPROGRAM|query|40|896|{}|0|330|323\n",
        records.len()
    );
    for (i, instruction) in records.iter().enumerate() {
        out.push_str(&format!("CODE|query|{i}|{instruction}\n"));
    }
    out.push_str(&format!("END|query|{}\n", records.len()));
    out
}

fn imported(text: &str) -> Result<lean_eth_reference::bit_program::Program<40, 896>, Error> {
    import_query_table(Cursor::new(text), ImportLimits::default())
}

#[test]
fn tiny_native_program_runs_from_source_defined_ports() {
    let p = imported(&table(&["set:0:1:1", "push:323:0:2", "halt"])).unwrap();
    assert_eq!(p.code().len(), 3);
    assert_eq!(
        (p.entry(), p.input_stack(), p.output_stack()),
        (0, 330, 323)
    );
    let mut config = p.initial([true, false]);
    let stats = p.run(&mut config, RunLimits::default()).unwrap();
    assert_eq!(stats.instructions, 3);
    assert_eq!(config.pc, None);
    assert_eq!(
        config.stacks[323].iter().copied().collect::<Vec<_>>(),
        [true]
    );
    assert_eq!(
        config.stacks[330].iter().copied().collect::<Vec<_>>(),
        [true, false]
    );
}

#[test]
fn every_source_instr_constructor_decodes_to_the_exact_rust_variant() {
    let rows = [
        "set:0:1:1",
        "copy:1:0:2",
        "not:2:1:3",
        "and:3:1:2:4",
        "or:4:3:2:5",
        "xor:5:1:2:6",
        "branch:5:7:8",
        "goto:9",
        "push:330:1:10",
        "peek:330:6:7:11",
        "pop:330:6:7:11",
        "halt",
    ];
    let p = imported(&table(&rows)).unwrap();
    assert_eq!(
        p.code(),
        &[
            Instr::Set {
                dst: 0,
                value: true,
                next: 1
            },
            Instr::Copy {
                dst: 1,
                src: 0,
                next: 2
            },
            Instr::Not {
                dst: 2,
                src: 1,
                next: 3
            },
            Instr::And {
                dst: 3,
                left: 1,
                right: 2,
                next: 4
            },
            Instr::Or {
                dst: 4,
                left: 3,
                right: 2,
                next: 5
            },
            Instr::Xor {
                dst: 5,
                left: 1,
                right: 2,
                next: 6
            },
            Instr::Branch {
                test: 5,
                yes: 7,
                no: 8
            },
            Instr::Goto { next: 9 },
            Instr::Push {
                stack: 330,
                src: 1,
                next: 10
            },
            Instr::Peek {
                stack: 330,
                value: 6,
                present: 7,
                next: 11
            },
            Instr::Pop {
                stack: 330,
                value: 6,
                present: 7,
                next: 11
            },
            Instr::Halt,
        ]
    );
    let mut config = p.initial([true, false]);
    p.run(&mut config, RunLimits::default()).unwrap();
    assert_eq!(config.pc, None);
    assert!(config.regs[5]);
    assert!(config.regs[6]);
    assert!(config.regs[7]);
    assert_eq!(
        config.stacks[330].iter().copied().collect::<Vec<_>>(),
        [true, false]
    );
}

#[test]
fn malformed_or_unpinned_tables_are_not_accepted() {
    let valid = table(&["set:0:1:1", "push:323:0:2", "halt"]);
    let cases = [
        valid.replacen(SOURCE_COMMIT, "deadbeef", 1),
        valid.replacen(QUERY_SOURCE_BLOB, "deadbeef", 1),
        valid.replace("PROGRAM|query|40|896", "PROGRAM|query|80|896"),
        valid.replace("PROGRAM|query|40|896|3", "PROGRAM|query|40|896|4"),
        valid.replace("CODE|query|1|", "CODE|query|0|"),
        valid.replace("push:323:0:2", "push:900:0:2"),
        valid.replace("set:0:1:1", "set:0:true:1"),
        valid.replace("set:0:1:1", "set:0:1:09"),
        valid.replace("set:0:1:1", "set:0:1:999"),
        valid.replace("push:323:0:2", "unknown:323:0:2"),
        valid.replace("END|query|3", "END|query|2"),
        valid.replace("END|query|3\n", ""),
        valid.clone() + "\n",
        valid.replace("CODE|query|1|push", "CODE|other|1|push"),
        valid.replace('0', "００"),
        valid.replace('\n', "\r\n"),
    ];
    for (i, text) in cases.iter().enumerate() {
        assert!(
            imported(text).is_err(),
            "invalid case {i} was accepted: {text:?}"
        );
    }
}

#[test]
fn resource_budgets_reject_valid_but_oversized_input() {
    let table = table(&["set:0:1:1", "push:323:0:2", "halt"]);
    for limits in [
        ImportLimits {
            max_labels: 2,
            max_bytes: 10_000,
        },
        ImportLimits {
            max_labels: 10,
            max_bytes: 25,
        },
        ImportLimits {
            max_labels: 0,
            max_bytes: 10000,
        },
    ] {
        assert!(matches!(
            import_query_table(Cursor::new(&table), limits),
            Err(Error::Capacity(_))
        ));
    }
}

#[test]
fn runtime_budget_refuses_without_a_successful_halt() {
    let p = imported(&table(&["goto:0", "halt"])).unwrap();
    let mut config = p.initial([]);
    assert!(matches!(
        p.run(
            &mut config,
            RunLimits {
                max_steps: 10,
                max_stack_bits: 10
            }
        ),
        Err(Error::Capacity(_))
    ));
    assert!(config.pc.is_some());
}
