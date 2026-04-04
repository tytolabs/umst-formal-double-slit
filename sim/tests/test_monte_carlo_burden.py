"""10k-run Monte Carlo burden check (Wave 6)."""

import importlib.util
import unittest
from pathlib import Path

_SIM = Path(__file__).resolve().parents[1] / "monte_carlo_burden.py"
_spec = importlib.util.spec_from_file_location("monte_carlo_burden", _SIM)
assert _spec and _spec.loader
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)


class MonteCarloBurdenTests(unittest.TestCase):
    def test_burden_monte_carlo_10k(self):
        out = _mod.run_monte_carlo(n_runs=10_000, seed=7, b0=2.0, mu=0.01, sigma=0.15)
        self.assertEqual(out["n_runs"], 10_000)
        self.assertLess(abs(out["mean_b1"] - out["predicted_e_b1"]), 0.02)


if __name__ == "__main__":
    unittest.main()
