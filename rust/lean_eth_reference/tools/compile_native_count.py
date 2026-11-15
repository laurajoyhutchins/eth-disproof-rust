#!/usr/bin/env python3
"""Compile the ORIGINAL composed high-query -> leaf -> DFS -> outer command.

The generated executable uses DeferredProgram's physical instruction semantics.
It never replaces a source call with a host-level SAT/count oracle. Source-graph
export failures or Cargo failures are refusals, not successful count results.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from export_compiled_batch import atomic_write, ensure_pinned
from extract_compiled_catalog import blob_hash
from run_source_graph_batch import LEAN
from source_graph_kernel_certificate import certificate_source
from temporary_rust_crate import isolated_cargo_manifest
from verify_source_graph import (
    MAX_NODES, MAX_SOURCE_LABELS, SOURCE_SHA, closed_keys,
    insist, number, parse_node, parse_source_graph_json,
)

MODULE = 'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuter'
LEAF = 'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram'
FQN = 'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountingExecutable.program'
IDENTITY = 'native_complete_counting'
LARGE_FQN = 'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountingExecutable.largeOnlyProgram'
LARGE_IDENTITY = 'native_large_domain_counting'
R, S, INPUT, OUTPUT = 80, 1220, 256, 1216


def lean_wrapper(k: int, cutoff: int) -> str:
    if not (2 <= k <= 8 and 0 <= cutoff <= 128):
        raise ValueError('unsafe count compilation parameters')
    return (
        f'import {MODULE}\n'
        f'import {LEAF}\n'
        'namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountingExecutable\n'
        'open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace\n'
        'open BitProgram StructuredCalls\n'
        '-- This is exactly Native.countingProgram cutoff k (NativeLeafProgram.command k).\n'
        '-- Inline its defining expression so the exporter sees the real Cmd tree.\n'
        'noncomputable def program :=\n'
        f'  compiled (Native.entryCommand {cutoff}\n'
        f'    (Native.outerCommand {k} (NativeLeafProgram.command {k})))\n'
        '    ABI.countStack ABI.answerStack\n'
        'end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountingExecutable\n'
    )



def large_only_wrapper(k: int, cutoff: int) -> str:
    """Compile the source-defined large branch with the original cutoff scan.

    The large branch of FiniteFallback.dispatchCommand is structurally the
    original outerCommand. Only the unexecutable small *yes* arm is replaced
    by skip; the emitted Rust binary refuses n<=cutoff before execution.
    A Lean lemma below proves the two branches have identical data-state
    execution under the original false cutoff flag. The physical label
    tables intentionally differ, so this is not a full program-code identity.
    """
    if not (2 <= k <= 8 and 0 <= cutoff <= 128):
        raise ValueError('unsafe count compilation parameters')
    return (
        f'import {MODULE}\n'
        f'import {LEAF}\n'
        'namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountingExecutable\n'
        'open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace\n'
        'open BitProgram StructuredCalls\n'
        '-- Source-defined large-input path with its real cutoff scanner.\n'
        '-- The unexecutable finite fallback is explicitly unsupported.\n'
        'noncomputable def largeOnlyProgram :=\n'
        '  compiled (.seq Native.frontendCommand\n'
        f'    (.seq (FiniteFallback.cutoffCommand {cutoff})\n'
        '      (.ite 75 (.base .skip)\n'
        f'        (Native.outerCommand {k} (NativeLeafProgram.command {k})))))\n'
        '    ABI.countStack ABI.answerStack\n'
        '\n'
        '-- This is a data-state refinement for the false cutoff branch,\n'
        '-- not equality of absolute machine labels or a counting theorem.\n'
        'theorem largeOnlyBranch_execution_eq_original\n'
        '    (B : Nat) (large : Cmd 80 1220) (a b c d : State 80 1220)\n'
        '    (tf tc tl : Nat)\n'
        '    (hf : Eval Native.frontendCommand tf a b)\n'
        '    (hc : Eval (FiniteFallback.cutoffCommand B) tc b c)\n'
        '    (hfalse : c.regs 75 = false)\n'
        '    (hl : Eval large tl c d) :\n'
        '    Eval (Native.entryCommand B large) (tf + (tc + (tl + 1))) a d ∧\n'
        '    Eval (.seq Native.frontendCommand\n'
        '      (.seq (FiniteFallback.cutoffCommand B)\n'
        '        (.ite 75 (.base .skip) large)))\n'
        '      (tf + (tc + (tl + 1))) a d := by\n'
        '  constructor\n'
        '  · change Eval (.seq Native.frontendCommand\n'
        '      (.seq (FiniteFallback.cutoffCommand B)\n'
        '        (.ite 75 (FiniteFallback.framedCommand B) large)))\n'
        '      (tf + (tc + (tl + 1))) a d\n'
        '    exact hf.seq (hc.seq\n'
        '      (hl.ite_false (yes := FiniteFallback.framedCommand B) hfalse))\n'
        '  · exact hf.seq (hc.seq\n'
        '      (hl.ite_false (yes := .base .skip) hfalse))\n'
        'end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountingExecutable\n'
    )


def mode_identity(mode: str) -> tuple[str, str]:
    if mode == 'full':
        return FQN, IDENTITY
    if mode == 'large-domain':
        return LARGE_FQN, LARGE_IDENTITY
    raise ValueError('unknown source counting entry mode')


def inspect_graph(raw: bytes, source_blob: str, *, mode: str = 'full'):
    fqn, identity = mode_identity(mode)
    graph = parse_source_graph_json(raw)
    closed_keys(graph, {'kind', 'source_commit', 'source_blob', 'declaration',
                        'id', 'abi', 'command'})
    insist(graph['kind'] == 'original-structured-source-v1', 'wrong graph protocol')
    insist(graph['source_commit'] == SOURCE_SHA and
           graph['source_blob'] == source_blob and
           graph['declaration'] == fqn and graph['id'] == identity,
           'graph is not the pinned selected original counting declaration')
    abi = graph['abi']
    closed_keys(abi, {'r', 's', 'labels', 'input', 'output'})
    r = number(abi['r'], 256, 'r')
    s = number(abi['s'], 4096, 's')
    labels = number(abi['labels'], MAX_SOURCE_LABELS, 'labels')
    inp = number(abi['input'], s, 'input')
    out = number(abi['output'], s, 'output')
    insist((r, s, inp, out) == (R, S, INPUT, OUTPUT),
           'whole counter has incorrect physical input/output ABI')
    root = parse_node(graph['command'], r, s, [MAX_NODES])
    insist(root.size + 1 == labels and 0 <= root.entry(1, 0) < labels,
           'whole counter has inconsistent source physical label count')
    return graph, root


def rust_binary(source_blob: str, graph_sha256: str, width: int = 3,
                cutoff: int = 20, *, mode: str = 'full') -> str:
    """Generate only the input/output CLI; source opcodes belong to Rust.

    Every supported original ProgramLinking node is decoded by the same
    Rust source-json loader, with a pinned source blob and graph digest.
    Python is not a second compiler backend or a source instruction oracle.
    """
    fqn, identity = mode_identity(mode)
    if not (2 <= width <= 8 and 0 <= cutoff <= 128):
        raise ValueError('unsafe count compilation parameters')
    if (len(source_blob) != 40 or
            any(c not in '0123456789abcdef' for c in source_blob) or
            len(graph_sha256) != 64 or
            any(c not in '0123456789abcdef' for c in graph_sha256)):
        raise ValueError('noncanonical source provenance for compiled count')
    return '\n'.join([
        '//! Native source-JSON backed counting CLI, not a Python source translator.',
        'use std::io::{self, Read};',
        'use std::sync::Arc;',
        'use lean_eth_reference::{parse_dimacs, Error};',
        'use lean_eth_reference::native_terminal_count::count_word_decimal;',
        'use lean_eth_reference::bit_program::{DeferredProgram, RunLimits, SourceGraphBinding};',
        f'fn original() -> Result<Arc<DeferredProgram<{R},{S}>>, Error> {{',
        '    DeferredProgram::from_original_source_json(include_bytes!("count.graph.json"), SourceGraphBinding {',
        f'        id: "{identity}",',
        f'        declaration: "{fqn}",',
        f'        source_blob: "{source_blob}",',
        f'        graph_sha256: "{graph_sha256}",',
        '    })',
        '}',
        'fn execute() -> Result<(), String> {',
        '    let mut args = std::env::args().skip(1);',
        '    let mut limits = RunLimits { max_steps: 100_000_000, max_stack_bits: 2_000_000 };',
        '    while let Some(key) = args.next() {',
        '        if key == "--help" || key == "-h" {',
        '            println!("Usage: eth-count [--max-steps N] [--max-stack-bits N] < input.cnf");',
        '            return Ok(());',
        '        }',
        '        let value = args.next().ok_or_else(|| format!("missing value for {key}"))?;',
        '        match key.as_str() {',
        '            "--max-steps" => limits.max_steps = value.parse::<u64>()',
        '                .map_err(|_| "invalid step budget")?,',
        '            "--max-stack-bits" => limits.max_stack_bits = value.parse::<usize>()',
        '                .map_err(|_| "invalid stack budget")?,',
        '            _ => return Err(format!("unknown option {key}")),',
        '        }',
        '    }',
        '    let mut text = String::new();',
        '    io::stdin().read_to_string(&mut text).map_err(|e| e.to_string())?;',
        '    let cnf = parse_dimacs(&text).map_err(|e| e.to_string())?;',
        f'    if cnf.variables() <= {cutoff} {{',
        f'        return Err("unsupported noncomputable finite fallback: n <= {cutoff}".into());',
        '    }',
        f'    if cnf.clauses().iter().any(|clause| clause.literals().len() > {width}) {{',
        '        return Err("formula exceeds compiled clause-width bound".into());',
        '    }',
        '    let program = original().map_err(|e| e.to_string())?;',
        '    let bits = cnf.encode_lean();',
        '    let mut state = program.initial(bits.bytes().map(|b| b == b\'1\'));',
        '    let stats = program.run(&mut state, limits).map_err(|e| e.to_string())?;',
        '    if state.pc.is_some() { return Err("source machine did not halt".into()); }',
        f'    let count = state.stacks[{INPUT}].iter().copied().collect::<Vec<_>>();',
        f'    let answer = state.stacks[{OUTPUT}].iter().copied().collect::<Vec<_>>();',
        '    if answer.len() != 1 || answer[0] != count.iter().any(|&bit| bit) {',
        '        return Err("source count/positivity outputs disagree".into());',
        '    }',
        '    println!("status=physical-' + ('large-domain-' if mode == 'large-domain' else '') + 'count-complete");',
        '    println!("count={}", count_word_decimal(&count));',
        '    println!("answer={}", u8::from(answer[0]));',
        '    println!("source_instructions={}", stats.instructions);',
        '    println!("peak_live_stack_bits={}", stats.peak_stack_bits);',
        '    println!("resource_basis=BitProgram_source_instructions_not_TM2_microsteps");',
        '    Ok(())',
        '}',
        'fn main() {',
        '    if let Err(error) = execute() {',
        '        eprintln!("eth-count: {error}");',
        '        std::process::exit(2);',
        '    }',
        '}',
        '',
    ])


def run_command(args, *, cwd: Path, timeout: int, env=None):
    result = subprocess.run(args, cwd=cwd, env=env, capture_output=True,
                            text=True, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f'{args[0]} failed: ' + result.stdout[-1500:] +
                           result.stderr[-2500:])
    return result.stdout


def compile_counting(a):
    # Invalidate stale results before a new attempt. A failed new build must
    # never leave an old executable or success receipt appearing current.
    a.output_dir.mkdir(parents=True, exist_ok=True)
    for name in ('eth-count', 'count.graph.json', 'eth-count.generated.rs',
                 'count.receipt.json'):
        (a.output_dir / name).unlink(missing_ok=True)
    upstream, lake_root, rust_crate = (p.resolve() for p in
                                      (a.upstream, a.lake_root, a.rust_crate))
    pin = ensure_pinned(upstream, lake_root)
    # Source identity is the immutable original NativeOuter module, not the
    # synthetic wrapper. The pinned repository fixes all imported dependencies.
    source_path = upstream / 'lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeOuter.lean'
    original_blob = blob_hash(source_path.read_bytes())
    insist(source_path.is_file() and len(original_blob) == 40, 'original NativeOuter missing')
    mode = getattr(a, 'entry_mode', 'full')
    fqn, identity = mode_identity(mode)
    wrapper = (lean_wrapper(a.width, a.cutoff) if mode == 'full'
               else large_only_wrapper(a.width, a.cutoff))
    definitions = wrapper.split('namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountingExecutable', 1)[1]
    # Exporter imports precede the synthetic original-expression wrapper.
    source = (f'import {MODULE}\nimport {LEAF}\n' +
              LEAN.read_text() + '\n' +
              'namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountingExecutable' +
              definitions +
              '\nset_option maxHeartbeats 2000000\n' +
              f'#export_original_source_graph {fqn} "{identity}" "{original_blob}"\n')
    with tempfile.TemporaryDirectory(prefix='native-count-', dir=lake_root) as scratch:
        work = Path(scratch)
        probe = work / 'SourceCounting.lean'
        probe.write_text(source, encoding='utf-8')
        if getattr(a, 'source_graph', None) is None:
            # Cold builds can exceed the source-export budget. Consumers of
            # the pinned graph probe may reuse its exact serialized result.
            run_command(['lake', '-K', 'maxJobs=2', 'build', MODULE, LEAF],
                        cwd=lake_root, timeout=a.timeout_seconds)
            raw = run_command(['lake', 'env', 'lean', str(probe)],
                              cwd=lake_root, timeout=a.timeout_seconds,
                              env={**os.environ, 'ORIGINAL_MAX_LABELS': '8192'}).encode('ascii')
        else:
            raw = a.source_graph.resolve().read_bytes()
        # Strictly check the full mode-specific declaration, source commit,
        # original Git blob, physical ABI and every serialized node. This is
        # necessary even when a graph came from a previous CI step.
        graph, root = inspect_graph(raw, original_blob, mode=mode)
        (work / 'count.graph.json').write_bytes(raw)
        record = {'id': identity, 'fqn': fqn, 'module': MODULE, 'git_blob': original_blob}
        cert_status = 'NOT_KERNEL_CERTIFIED'
        if a.require_certificate:
            certificate, receipt = certificate_source(work / 'count.graph.json', record)
            # The synthetic wrapper is part of the proof input, not part of
            # the original OpenAI tree. Its exact bytes are receipt-bound.
            certificate = certificate.replace(f'import {MODULE}\n',
                                              wrapper + '\n', 1)
            proof = work / 'CountCertificate.lean'
            proof.write_text(certificate, encoding='utf-8')
            run_command(['lake', 'env', 'lean', str(proof)],
                        cwd=lake_root, timeout=a.timeout_seconds)
            cert_status = 'LEAN_KERNEL_CERTIFIED_SOURCE_DERIVED_COUNT'
        generated = rust_binary(original_blob, hashlib.sha256(raw).hexdigest(),
                                a.width, a.cutoff, mode=mode)
        crate = work / 'crate'
        (crate / 'src').mkdir(parents=True)
        (crate / 'src/main.rs').write_text(generated, encoding='utf-8')
        (crate / 'src/count.graph.json').write_bytes(raw)
        (crate / 'Cargo.toml').write_text(
            isolated_cargo_manifest('eth_native_count', rust_crate), encoding='utf-8')
        run_command(['cargo', 'build', '--offline', '--release',
                     '--manifest-path', str(crate / 'Cargo.toml')],
                    cwd=crate, timeout=a.timeout_seconds)
        executable = crate / 'target/release/eth_native_count'
        insist(executable.is_file(), 'cargo completed without the native count executable')
        receipt = {
            'status': 'COMPILED_SOURCE_COUNTING' if a.require_certificate
                      else 'COMPILED_SOURCE_COUNTING_UNCERTIFIED',
            'certificate_status': cert_status,
            'source_commit': SOURCE_SHA,
            'source_blob': original_blob,
            'declaration': fqn,
            'entry_mode': mode,
            'source_derived_wrapper_sha256': hashlib.sha256(wrapper.encode()).hexdigest(),
            'source_graph_sha256': hashlib.sha256(raw).hexdigest(),
            'generated_rust_sha256': hashlib.sha256(generated.encode()).hexdigest(),
            'rust_loader': 'original-structured-source-v1/serde-native',
            'labels': graph['abi']['labels'],
            'entry': root.entry(1, 0),
            'width': a.width, 'cutoff': a.cutoff,
            'input_stack': INPUT, 'count_stack': INPUT, 'answer_stack': OUTPUT,
            'resource_basis': 'physical BitProgram instructions; not TM2 microsteps',
            'limitations': [
                'no whole-program count correctness proof transferred to Rust',
                'selected cutoff is not established as the existential cutoff in original Final.lean',
                'source instruction counts are not primitive TM2 costs or complexity bounds',
                'the runtime refuses inputs at or below the selected cutoff',
            ] + (['large-domain command is not byte-identical to original entryCommand; only false-cutoff branch has source-level data-state refinement']
                 if mode == 'large-domain' else []) + ([] if a.require_certificate else [
                'synthetic wrapper source graph not separately Lean-kernel certified',
            ]),
        }
        # Publish the success receipt last; failures never produce one.
        path = a.output_dir / 'eth-count'
        shutil.copy2(executable, path)
        path.chmod(0o755)
        atomic_write(a.output_dir / 'count.graph.json', raw.decode('ascii'))
        atomic_write(a.output_dir / 'eth-count.generated.rs', generated)
        atomic_write(a.output_dir / 'count.receipt.json',
                     json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    return receipt


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('upstream', 'lake-root', 'rust-crate', 'output-dir'):
        p.add_argument('--' + name, required=True, type=Path)
    p.add_argument('--width', type=int, default=3)
    p.add_argument('--cutoff', type=int, default=20)
    p.add_argument('--entry-mode', choices=['full', 'large-domain'],
                   default='full', help='large-domain excludes the source noncomputable finite fallback and refuses n<=cutoff')
    p.add_argument('--timeout-seconds', type=int, default=1200)
    p.add_argument('--require-certificate', action='store_true')
    p.add_argument('--source-graph', type=Path,
                   help='reuse a previously exported exact pinned Lean graph instead of rebuilding')
    a = p.parse_args()
    if not (30 <= a.timeout_seconds <= 7200):
        p.error('timeout must be 30..7200 seconds')
    result = compile_counting(a)
    print('NATIVE_COUNT_COMPILED', result['labels'], result['status'], flush=True)


if __name__ == '__main__':
    main()
