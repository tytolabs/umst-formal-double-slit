# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Smoke test for benchmark_schrodinger_2d_split_step_vs_fd (needs SciPy)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD_PATH = ROOT / "sim" / "benchmark_schrodinger_2d_split_step_vs_fd.py"


def _have_scipy() -> bool:
    try:
        import scipy.linalg  # noqa: F401

        return True
    except ImportError:
        return False


def _load():
    spec = importlib.util.spec_from_file_location(
        "benchmark_schrodinger_2d_split_step_vs_fd",
        MOD_PATH,
    )
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(_have_scipy(), "scipy not installed")
class Benchmark2DSplitVsFDTests(unittest.TestCase):
    def test_compare_returns_finite_gap(self) -> None:
        m = _load()
        gap, ts, tf, nrm = m.compare_split_step_vs_fd(
            nx=8,
            ny=8,
            lx=8.0,
            ly=8.0,
            t=0.12,
            n_steps=24,
            v0=6.0,
        )
        self.assertGreaterEqual(gap, 0.0)
        self.assertTrue(gap == gap)
        self.assertGreaterEqual(ts, 0.0)
        self.assertGreaterEqual(tf, 0.0)
        self.assertAlmostEqual(nrm, 1.0, places=4)


if __name__ == "__main__":
    unittest.main()
