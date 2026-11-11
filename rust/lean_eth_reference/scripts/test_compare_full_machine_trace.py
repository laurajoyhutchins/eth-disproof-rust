"""Mutation checks for the full-state comparator. Requires no Lean cache."""
import importlib.util
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

SCRIPT = Path(__file__).with_name('compare-full-machine-trace.py')
spec = importlib.util.spec_from_file_location('full_trace_comparator', SCRIPT)
assert spec and spec.loader
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def fixture():
    lines = []
    for size in range(5):
        for code in range(1 << size):
            for mode in ('clean', 'dirty'):
                name = f'{size}_{code}_{mode}'
                lines.append(f'machine|{name}|0|0|00||')
                lines.append(f'machine|{name}|1|H|00||')
    return lines


class ComparatorTests(unittest.TestCase):
    def test_accepts_matching_complete_stream(self):
        with TemporaryDirectory() as d:
            p = Path(d) / 'trace'
            p.write_text('\n'.join(fixture())+'\n')
            self.assertEqual(mod.compare(p,p), (62,124))

    def test_rejects_omitted_case(self):
        with TemporaryDirectory() as d:
            p=Path(d)/'trace'
            p.write_text('\n'.join(fixture()[2:])+'\n')
            with self.assertRaises(ValueError): mod.parse(p)

    def test_rejects_changed_register_even_when_terminal_matches(self):
        with TemporaryDirectory() as d:
            a,b=Path(d)/'a',Path(d)/'b'
            lines=fixture(); a.write_text('\n'.join(lines)+'\n')
            lines[0]=lines[0].replace('|00||', '|10||')
            b.write_text('\n'.join(lines)+'\n')
            with self.assertRaises(AssertionError): mod.compare(a,b)

    def test_rejects_repeated_or_missing_step(self):
        with TemporaryDirectory() as d:
            p=Path(d)/'trace'; lines=fixture()
            lines[1]=lines[1].replace('|1|H|', '|2|H|')
            p.write_text('\n'.join(lines)+'\n')
            with self.assertRaises(ValueError): mod.parse(p)

    def test_rejects_unfinished_run(self):
        with TemporaryDirectory() as d:
            p=Path(d)/'trace'; lines=fixture()
            lines[1]=lines[1].replace('|H|', '|1|')
            p.write_text('\n'.join(lines)+'\n')
            with self.assertRaises(ValueError): mod.parse(p)


if __name__ == '__main__': unittest.main()
