import json
import tempfile
import unittest
from pathlib import Path
from validate import read_graph, project_view

ROOT = Path(__file__).parent

class GraphTests(unittest.TestCase):
    def test_compiled_smoke(self):
        path = ROOT / "smoke.jsonl"
        if not path.exists():
            self.skipTest("Generate with: LEAN_PATH=. lean --run Extract.lean Smoke smoke.jsonl ProofGraphSmoke.twice")
        manifest, nodes, edges = read_graph(path)
        self.assertEqual(manifest["roots"], ["ProofGraphSmoke.twice"])
        self.assertIn("ProofGraphSmoke.double", nodes)
        self.assertIn("ProofGraphSmoke.double", nodes["ProofGraphSmoke.twice"]["value_refs"])
        self.assertGreater(edges, 50)
        view = project_view(path, ["Smoke"], {
            "source_sha": "local-smoke", "mathlib_sha": "not-used", "lean_version": "4.34.1",
        })
        self.assertEqual(view["counts"]["project_nodes"], 2)
        self.assertTrue(view["raw_complete"])
        self.assertEqual(view["counts"]["project_nodes"] + view["counts"]["external_boundary_nodes"], len(view["nodes"]))

    def test_refuse_interrupted_export(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "partial.jsonl"
            path.write_text(json.dumps({"kind":"manifest","complete":False,"roots":["demo"]})+"\n")
            with self.assertRaisesRegex(ValueError, "incomplete"):
                read_graph(path)

    def test_refuse_nonexistent_reference(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "bad.jsonl"
            records = [
                {"kind":"manifest","complete":False,"roots":["demo"]},
                {"id":"demo","module":"Demo","kind":"theorem","type_refs":["missing"],"value_refs":[]},
                {"kind":"complete","nodes":1,"edges":1,"roots":["demo"]},
            ]
            path.write_text("\n".join(json.dumps(row) for row in records)+"\n")
            with self.assertRaisesRegex(ValueError, "unresolved"):
                read_graph(path)

if __name__ == "__main__":
    unittest.main()
