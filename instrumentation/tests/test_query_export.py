"""Offline format and provenance refusal tests; no synthetic Lean acceptance."""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import export_query_table as target  # noqa: E402


class QueryExportTest(unittest.TestCase):
    def table(self, suffix: bytes = b"") -> bytes:
        return (
            f"PIN|query|{target.SOURCE}|{target.BLOB}\n"
            "PROGRAM|query|40|896|2|0|330|323\n"
            "CODE|query|0|set:0:1:1\n"
            "CODE|query|1|halt\n"
            "END|query|2\n"
        ).encode() + suffix

    def check(self, data: bytes, cap: int = 3) -> int:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "query.table"
            path.write_bytes(data)
            return target.verify_stream(path, cap)

    def test_complete_and_ordered_sample(self) -> None:
        self.assertEqual(self.check(self.table()), 2)

    def test_wrong_pin_missing_end_and_trailing_bytes_refuse(self) -> None:
        self.assertRaises(RuntimeError, self.check, self.table().replace(target.SOURCE.encode(), b"BAD"))
        self.assertRaises(RuntimeError, self.check, self.table().replace(b"CODE|query|1", b"CODE|query|0"))
        self.assertRaises(RuntimeError, self.check, self.table().replace(b"END|query|2\n", b""))
        self.assertRaises(RuntimeError, self.check, self.table(b"EXTRA\n"))

    def test_label_cap_refuses(self) -> None:
        self.assertRaises(RuntimeError, self.check, self.table(), 1)

    def test_minimal_lake_root_checks_actual_mathlib_checkout(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            original = root / "openai-math"
            original_oai = original / "lean" / "OAI"
            original_oai.mkdir(parents=True)
            lake = root / "pinned-lake"
            lake.mkdir()
            (lake / "OAI").symlink_to(original_oai, target_is_directory=True)
            mathlib = lake / ".lake" / "packages" / "mathlib"
            mathlib.mkdir(parents=True)
            probe = root / "probe.lean"
            probe.write_text("-- pinned probe\n", encoding="utf-8")
            commands: list[tuple[tuple[str, ...], Path]] = []

            def command(*args: str, cwd: Path) -> str:
                commands.append((args, cwd))
                if cwd == original:
                    if args == ("git", "rev-parse", "HEAD"):
                        return target.SOURCE
                    if args == ("git", "rev-parse", f"HEAD:{target.SOURCE_PATH}"):
                        return target.BLOB
                    if args == ("git", "status", "--porcelain", "--untracked-files=no"):
                        return ""
                if cwd == mathlib:
                    if args == ("git", "rev-parse", "HEAD"):
                        return target.MATHLIB_SHA
                    if args == ("git", "status", "--porcelain", "--untracked-files=no"):
                        return ""
                if cwd == lake and args == ("lake", "env", "lean", "--version"):
                    return "Lean (version 4.34.1, x86_64-unknown-linux-gnu)"
                raise AssertionError(f"unexpected command {args!r} in {cwd}")

            with (
                mock.patch.object(target, "UPSTREAM", original),
                mock.patch.object(target, "LAKE", original / "lean"),
                mock.patch.object(target, "PROBE", probe),
                mock.patch.object(target, "command", side_effect=command),
            ):
                identity = target.verified_identity(lake)
            self.assertEqual(identity["mathlib_commit"], target.MATHLIB_SHA)
            self.assertIn(
                (("git", "status", "--porcelain", "--untracked-files=no"), mathlib),
                commands,
            )

    def test_unpinned_git_commit_refuses_before_export(self) -> None:
        with mock.patch.object(target, "command", return_value="wrong"):
            with self.assertRaisesRegex(RuntimeError, "unpinned original OpenAI"):
                target.verified_identity()


if __name__ == "__main__":
    unittest.main()
