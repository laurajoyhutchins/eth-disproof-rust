"""Adversarial tests for the exact original fixed-bank compiler fragment."""
import unittest

from prepare_clear_expansion import (
    adjacent_seq, clear_call, leaf_ports,
    require_original_bank_recursion, require_original_clear_program,
)


CLEAR = """abbrev clearProgram {r s : ℕ} (src : Fin s) (value present : Fin r) : Program r s 3 where
  inputStack := src
  outputStack := src
  entry := 0
  code := ![.pop src value present 1, .branch present 0 2, .halt]

"""
BANK = """def clearCmd {r s : ℕ} (tmp : Fin s) (value present : Fin r) :
    List (Fin s) → Cmd r s
  | [] => .call (clearProgram tmp value present)
  | dst :: ports => .seq (.call (clearProgram dst value present))
      (clearCmd tmp value present ports)

"""


class OriginalClearExpansionTests(unittest.TestCase):
    def test_original_source_constructors_are_exact(self):
        require_original_clear_program(CLEAR)
        require_original_bank_recursion(BANK)

    def test_unsupported_source_changes_refuse(self):
        for orig, changed, validator in [
            (CLEAR, CLEAR.replace(".pop", ".peek"), require_original_clear_program),
            (CLEAR, CLEAR.replace(".branch present 0 2",
                                  ".branch present 2 0"), require_original_clear_program),
            (CLEAR, CLEAR.replace("entry := 0", "entry := 1"),
             require_original_clear_program),
            (BANK, BANK.replace("dst :: ports", "ports"), require_original_bank_recursion),
            (BANK, BANK.replace("clearProgram tmp", "clearProgram dst"),
             require_original_bank_recursion),
            (BANK, BANK.replace("clearCmd tmp", "clearCmd dst"),
             require_original_bank_recursion),
        ]:
            self.assertNotEqual(orig, changed)
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                validator(changed)

    def test_exact_table_and_ordered_balanced_expansion(self):
        ports = [104, 5, 323, 329]
        bank = adjacent_seq([clear_call(p) for p in ports + [699]])
        prepare = adjacent_seq([clear_call(p) for p in [699] + ports + [699]])
        self.assertEqual(leaf_ports(bank), ports + [699])
        self.assertEqual(leaf_ports(prepare), [699] + ports + [699])
        self.assertEqual(clear_call(5)["program"]["code"],
                         ["pop:5:0:1:1", "branch:1:0:2", "halt"])

    def test_invalid_tables_and_source_addresses_refuse(self):
        for src in (-1, 768, None, True, 1.1):
            with self.subTest(src=src), self.assertRaises(ValueError):
                clear_call(src)
        for change in ("wrong_label", "wrong_pop", "fake_kind", "extra"):
            node = clear_call(10)
            if change == "wrong_label":
                node["program"]["code"][1] = "branch:1:2:0"
            elif change == "wrong_pop":
                node["program"]["code"][0] = "pop:11:0:1:1"
            elif change == "fake_kind":
                node["kind"] = "atom"
            else:
                node["program"]["source_certified"] = True
            with self.subTest(change=change), self.assertRaises(ValueError):
                leaf_ports(node)
        with self.assertRaises(ValueError):
            adjacent_seq([])


if __name__ == "__main__":
    unittest.main()
