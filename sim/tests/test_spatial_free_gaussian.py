"""Regression tests for spatial_free_gaussian_1d (stdlib only)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "sim" / "spatial_free_gaussian_1d.py"


def _load_mod():
    spec = importlib.util.spec_from_file_location("spatial_free_gaussian_1d", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(module)
    return module


class TestSpatialFreeGaussian(unittest.TestCase):
    def test_density_nonnegative(self) -> None:
        m = _load_mod()
        for x in (-3.0, 0.0, 2.5):
            self.assertGreaterEqual(m.density(x, 0.5), 0.0)

    def test_validate_normalization_t0(self) -> None:
        m = _load_mod()
        integral, peak = m.validate_normalization(
            t=0.0,
            x0=0.0,
            k0=0.0,
            sigma0=1.0,
            half_width=14.0,
            n_points=20001,
        )
        self.assertAlmostEqual(integral, 1.0, places=3)
        self.assertGreater(peak, 0.0)

    def test_validate_normalization_spread(self) -> None:
        m = _load_mod()
        integral, _ = m.validate_normalization(
            t=2.0,
            x0=0.0,
            k0=0.3,
            sigma0=0.8,
            half_width=18.0,
            n_points=24001,
        )
        self.assertAlmostEqual(integral, 1.0, places=3)


if __name__ == "__main__":
    unittest.main()
