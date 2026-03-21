"""Tests for classical_double_slit_far_field (stdlib)."""

import importlib.util
import math
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "sim" / "classical_double_slit_far_field.py"


def _load_mod():
    spec = importlib.util.spec_from_file_location("classical_double_slit_far_field", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(module)
    return module


class TestClassicalDoubleSlitFarField(unittest.TestCase):
    def test_peak_normalized(self) -> None:
        m = _load_mod()
        lam, a, d = 500e-9, 8e-6, 80e-6
        self.assertAlmostEqual(m.intensity_normalized(0.0, lam, a, d), 1.0, places=10)

    def test_symmetry_and_nonneg(self) -> None:
        m = _load_mod()
        lam, a, d = 600e-9, 12e-6, 120e-6
        for k in range(1, 50):
            u = 0.0001 * k
            i_p = m.intensity_normalized(u, lam, a, d)
            i_m = m.intensity_normalized(-u, lam, a, d)
            self.assertGreaterEqual(i_p, -1e-15)
            self.assertAlmostEqual(i_p, i_m, places=10)

    def test_sinc_limit(self) -> None:
        m = _load_mod()
        self.assertAlmostEqual(m.sinc_ratio(0.0), 1.0, places=14)
        x = 0.3
        self.assertAlmostEqual(m.sinc_ratio(x), math.sin(x) / x, places=14)


if __name__ == "__main__":
    unittest.main()
