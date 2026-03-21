# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Absorbing edge mask + split-step (optional NumPy)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD = ROOT / "sim" / "schrodinger_1d_absorbing_edges.py"


def _have_numpy() -> bool:
    try:
        import numpy as _np  # noqa: F401

        return True
    except ImportError:
        return False


def _load():
    spec = importlib.util.spec_from_file_location("schrodinger_1d_absorbing_edges", MOD)
    m = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(m)
    return m


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class AbsorbingEdgesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_mask_interior_one(self) -> None:
        np = self.np
        m = _load()
        mask = m.absorption_mask(100, 10, 0.5)
        self.assertTrue(np.all(mask[10:-10] == 1.0))
        self.assertAlmostEqual(float(mask[0]), 0.5, places=6)
        self.assertAlmostEqual(float(mask[-1]), 0.5, places=6)

    def test_zero_absorb_matches_split_step(self) -> None:
        np = self.np
        m = _load()
        sp = m._load_split()
        ff = m._load_fft()
        xs, dx = ff.make_grid(32.0, 512)
        v0 = np.zeros_like(xs)
        psi0 = ff.initial_gaussian(xs, x0=-4.0, k0=0.9, sigma0=0.85)
        psi0 = psi0 / np.sqrt(ff.norm_dx(psi0, dx))
        mask0 = m.absorption_mask(512, 0, 0.9)
        steps = 80
        dt = 0.5 / steps
        a = m.split_step_evolve_with_absorption(
            psi0, dx, dt=dt, n_steps=steps, v_x=v0, mask=mask0
        )
        b = sp.split_step_evolve(psi0, dx, dt=dt, n_steps=steps, v_x=v0)
        self.assertLess(float(np.max(np.abs(a - b))), 1e-9)

    def test_absorption_drops_norm(self) -> None:
        np = self.np
        m = _load()
        ff = m._load_fft()
        xs, dx = ff.make_grid(40.0, 1024)
        v0 = np.zeros_like(xs)
        x_right = float(xs[-1])
        psi0 = ff.initial_gaussian(xs, x0=x_right - 1.5, k0=0.7, sigma0=0.4)
        psi0 = psi0 / np.sqrt(ff.norm_dx(psi0, dx))
        mask = m.absorption_mask(1024, 64, 0.72)
        steps = 200
        dt = 1.4 / steps
        psi1 = m.split_step_evolve_with_absorption(
            psi0, dx, dt=dt, n_steps=steps, v_x=v0, mask=mask
        )
        self.assertLess(ff.norm_dx(psi1, dx), ff.norm_dx(psi0, dx) - 1e-3)


if __name__ == "__main__":
    unittest.main()
