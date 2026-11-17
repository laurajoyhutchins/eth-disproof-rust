"""Adversarial checks for source-compositional Count.Prepare port evaluation."""
import unittest

from prepare_ports_compositional import SOURCES, evaluate, literal


def source_fixture() -> dict[str, str]:
    return {
        "prepare": """def ports : List (Fin 768) :=
  (((ReconstructionProgram.NativeState.cleanPorts ++ ReconstructionProgram.InputReady.emptyPorts).map crtStacks) ++
    [323,324,325,326,327,328,329]).dedup

""",
        "state": """def workingClean : List (Fin 320) := Middle.cleanPorts ++
  CRTLocalProgram.localWork.map localPorts ++
  (List.ofFn fun i => localPorts (SubexpConvolutionControl.bufferPorts i))

def cleanPorts : List (Fin 320) := initialCleanPorts ++ workingClean ++ [5,10]

""",
        "middle": """def cleanPorts : List (Fin 320) :=
  CofactorOuter.cleanPorts ++ Scalar.cleanPorts ++ Horner.cleanPorts ++ [192,193,262,263,264]

""",
        "cofactor": """def cleanPorts : List (Fin 320) :=
  [120,121,122,215,217,218,219,223,229,240,241,244,245,246,262,318,319]

""",
        "scalar": "def cleanPorts : List (Fin 320) := [120,240,241,244,245,318,319]\n\n",
        "horner": """def cleanPorts : List (Fin 320) :=
  [120,240,241,245,246,247,248,250,251,252,264,318,319]

""",
        "initial": """def initialCleanPorts : List (Fin 320) :=
  [104,261,268,277,278,279,316,317,318,214,257,266] ++ [213,216,225,258,259,260]

""",
        "local_work": """def localWork : List (Fin 256) :=
  [100,101,102,107,108,120,121,122,205,208,215,217,218,219,220,222,223,
   224,227,228,229,240,241,242,244,245,246,247]

""",
        "local_ports": """def localPorts : Fin 256 ↪ Fin 320 := ⟨Fin.castAdd 64, Fin.castAdd_injective 256 64⟩

""",
        "buffer_ports": """def bufferPorts : Fin 11 ↪ Fin 256 :=
  ⟨![100, 101, 102, 103, 105, 106, 108, 109, 110, 198, 199], by decide⟩

""",
        "ready": """def emptyPorts : List (Fin 320) :=
  [0,1,2,3,4,6,7,8,9,11,12,13,112,113,114,115,116,117,118,119,120,
   128,129,130,131,132,134,135,136,137,138,139,141,142,143,144,
   146,147,148,149,151,152,153,154,155,156,157,158,159,198,199,200]

""",
        "crt_stacks": """def crtStacks (i : Fin 320) : Fin 768 := i.castAdd 448

""",
    }


class CompositionalPortTests(unittest.TestCase):
    def test_closed_source_fragment_and_lean_dedup_order(self):
        sources = source_fixture()
        self.assertEqual(set(sources), set(SOURCES))
        ports, trace = evaluate(sources)
        self.assertEqual(trace["result"], len(ports))
        self.assertEqual(trace["pre_dedup"] > len(ports), True)
        self.assertEqual(ports[-7:], list(range(323, 330)))
        self.assertEqual(len(ports), len(set(ports)))
        self.assertLess(max(ports), 330)
        self.assertNotIn(699, ports)
        # The first occurrence of 120 is removed by Lean List.dedup
        # because later occurrences exist in Scalar/Horner/local-work/ready.
        self.assertLess(ports.index(104), ports.index(120))
        self.assertGreater(ports.index(120), ports.index(119))

    def test_reject_nonliteral_or_out_of_bounds(self):
        for expr in ("[320]", "[3,-1]", "[1, two]", "List.range 320",
                     "[1, 1.5]", "[]"):
            with self.subTest(expr=expr), self.assertRaises(ValueError):
                literal(expr, 320)

    def test_unrecognized_original_operations_refuse(self):
        mutations = [
            ("prepare", ".dedup", ".reverse"),
            ("state", "List.ofFn", "List.range"),
            ("state", "localPorts", "otherPorts"),
            ("middle", "CofactorOuter.cleanPorts", "Scalar.cleanPorts"),
            ("initial", " ++ ", " -- "),
            ("local_work", "245,246,247", "245,246,300"),
            ("buffer_ports", "199", "260"),
            ("ready", "198,199,200", "198,199,321"),
            ("crt_stacks", "i.castAdd 448", "⟨448+i.val, by omega⟩"),
            ("local_ports", "Fin.castAdd 64", "Fin.castAdd 63"),
        ]
        for key, old, new in mutations:
            with self.subTest(key=key, change=new):
                sources = source_fixture()
                self.assertIn(old, sources[key])
                sources[key] = sources[key].replace(old, new, 1)
                with self.assertRaises(ValueError):
                    evaluate(sources)

    def test_incomplete_or_duplicate_declaration_refuses(self):
        original = source_fixture()
        with self.assertRaises(ValueError):
            evaluate({k: v for k, v in original.items() if k != "ready"})
        original["ready"] += original["ready"]
        with self.assertRaises(ValueError):
            evaluate(original)


if __name__ == "__main__":
    unittest.main()
