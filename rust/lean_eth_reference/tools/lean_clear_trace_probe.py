"""Strict shape checks for *actual* pinned Lean BitProgram.step trace output.

This tool does not emulate the transition relation. Rust independently runs the
physical source instructions and compares every resulting state to Lean's own
observations. Four finite cases are evidence, not a universal theorem.
"""
import argparse
import json
from pathlib import Path

PREFIX = "ORIGINAL_LEAN_CLEAR_TRACE="
SOURCE_COMMIT = "4eaee87548250b2682affda7d05d947c05554bae"
DECLARATION = "OAI.Algorithms.SubexponentialSAT.StackRoutines.clearProgram"
WORDS = [[], [True], [False, True], [True, False, True]]


def validate(stdout: str) -> dict:
    lines = [l[len(PREFIX):] for l in stdout.splitlines() if l.startswith(PREFIX)]
    if len(lines) != 1:
        raise ValueError("require exactly one genuine original Lean trace report")
    report = json.loads(lines[0])
    if (not isinstance(report, dict) or set(report) != {
            "format", "source_commit", "declaration",
            "r", "s", "labels", "source_stack",
            "value_register", "present_register", "cases",
            "independent_lean_rust_parity_proved"
    } or report["format"] != "original-lean-clearprogram-steps-v1" or
            report["source_commit"] != SOURCE_COMMIT or
            report["declaration"] != DECLARATION or
            (report["r"], report["s"], report["labels"]) != (3, 4, 3) or
            (report["source_stack"], report["value_register"],
             report["present_register"]) != (1, 0, 1) or
            report["independent_lean_rust_parity_proved"] is not False):
        raise ValueError("original Lean trace ABI or certification claim changed")
    cases = report["cases"]
    if not isinstance(cases, list) or len(cases) != len(WORDS):
        raise ValueError("original Lean trace case set changed")
    for index, (case, word) in enumerate(zip(cases, WORDS)):
        if not isinstance(case, dict) or set(case) != {"word", "states", "source_steps"}:
            raise ValueError(f"case {index} malformed")
        if (case["word"] != word or
                type(case["source_steps"]) is not int or
                case["source_steps"] != 2 * len(word) + 3):
            raise ValueError(f"case {index} source trace preconditions changed")
        states = case["states"]
        if not isinstance(states, list) or len(states) != case["source_steps"] + 1:
            raise ValueError(f"case {index} missing physical steps")
        for step, state in enumerate(states):
            if (not isinstance(state, dict) or set(state) != {"pc", "regs", "stacks"} or
                    state["pc"] is not None and
                    (type(state["pc"]) is not int or not 0 <= state["pc"] < 3) or
                    not isinstance(state["regs"], list) or len(state["regs"]) != 3 or
                    any(type(b) is not bool for b in state["regs"]) or
                    not isinstance(state["stacks"], list) or len(state["stacks"]) != 4 or
                    any(not isinstance(w, list) or
                        any(type(b) is not bool for b in w)
                        for w in state["stacks"])):
                raise ValueError(f"case {index} state {step} malformed")
        if states[0]["pc"] != 0 or states[-1]["pc"] is not None:
            raise ValueError(f"case {index} source halt boundary changed")
        if (states[0]["regs"] != [False, False, True] or
                states[0]["stacks"] != [[], word, [], [False, True]]):
            raise ValueError(f"case {index} original source initial state changed")
        if states[-1]["stacks"] != [[], [], [], [False, True]]:
            raise ValueError(f"case {index} original source clear result changed")
        if states[-1]["regs"] != [False, False, True]:
            raise ValueError(f"case {index} original source register reset changed")
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--stdout", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = validate(args.stdout.read_text())
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    print("ORIGINAL_LEAN_CLEAR_REFERENCE_OBSERVED samples=4 "
          "source_step_traces=true kernel_certificate=false")


if __name__ == "__main__":
    main()
