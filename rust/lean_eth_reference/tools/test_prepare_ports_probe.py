"""Negative regression checks for the separately evaluated original port list."""
import unittest

from prepare_ports_probe import PORT_NAME, PREFIX, validate


def source():
    return {
        "format": "original-query-kernel-root-v11",
        "status": "SOURCE_ROOT_INVENTORIED_UNVERIFIED",
        "source_prepare_obligation": {
            "bank_port_declaration": PORT_NAME,
            "bank_port_values_resolved": False,
        },
        "rust_executable": False,
        "receipt_is_kernel_certificate": False,
        "source_commit": "4eaee87548250b2682affda7d05d947c05554bae",
        "source_git_blob": "a" * 40,
        "original_olean_sha256": "f" * 64,
    }


class PortListTests(unittest.TestCase):
    def test_valid_original_shaped_observation_remains_uncertified(self):
        p = [190, 191, 323, 324, 325, 326, 327, 328, 329]
        r = validate(PREFIX + str(p).replace("'", '"'), source())
        self.assertEqual(r["ports"], p)
        self.assertFalse(r["rust_executable"])
        self.assertFalse(r["receipt_is_kernel_certificate"])

    def test_refuse_missing_duplicate_or_promoted_observations(self):
        base = [190, 323, 324, 325, 326, 327, 328, 329]
        for change in ("missing", "duplicate", "overbound", "scratch",
                       "noninteger", "mismatched_decl", "promoted_port",
                       "promoted_execution", "forged_certificate"):
            with self.subTest(change=change):
                data = list(base)
                receipt = source()
                if change == "missing":
                    data.remove(323)
                elif change == "duplicate":
                    data.append(190)
                elif change == "overbound":
                    data.append(330)
                elif change == "scratch":
                    data.append(699)
                elif change == "noninteger":
                    data.append(True)
                elif change == "mismatched_decl":
                    receipt["source_prepare_obligation"]["bank_port_declaration"] = "OAI.Forged.ports"
                elif change == "promoted_port":
                    receipt["source_prepare_obligation"]["bank_port_values_resolved"] = True
                elif change == "promoted_execution":
                    receipt["rust_executable"] = True
                else:
                    receipt["receipt_is_kernel_certificate"] = True
                with self.assertRaises(ValueError):
                    validate(PREFIX + __import__("json").dumps(data), receipt)


if __name__ == "__main__":
    unittest.main()
