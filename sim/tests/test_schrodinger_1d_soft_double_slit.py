# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Soft double-slit potential builder + smoke propagation (optional NumPy)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD_PATH = ROOT / "sim" / "schrodinger_1d_soft_double_slit.py"


def _have_numpy() -> bool:
    try:
        import numpy as _np  # noqa: F401

        return True
    except ImportError:
        return False


def _load():
    spec = importlib.util.spec_from_file_location("schrodinger_1d_soft_double_slit", MOD_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class SoftDoubleSlitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_potential_shape_and_screen(self) -> None:
        np = self.np
        m = _load()
        xs = np.linspace(-4.0, 4.0, 801)
        v = m.soft_double_slit_potential(
            xs, v0=10.0, x_screen=0.0, slit_separation=1.0, slit_sigma=0.2, slit_center_offset=0.2
        )
        self.assertEqual(v.shape, xs.shape)
        self.assertTrue(np.all(v[xs < 0.0] == 0.0))
        self.assertGreater(float(np.max(v)), 5.0)

    def test_propagate_norm_and_peaks(self) -> None:
        np = self.np
        m = _load()
        sp = m._load_split()
        ff = m._load_fft()
        xs, dx = ff.make_grid(52.0, 3072)
        v_x = m.soft_double_slit_potential(
            xs,
            v0=26.0,
            x_screen=-2.0,
            slit_separation=1.3,
            slit_sigma=0.21,
            slit_center_offset=0.3,
        )
        psi0 = ff.initial_gaussian(xs, x0=-16.0, k0=1.3, sigma0=1.05)
        psi0 = psi0 / np.sqrt(ff.norm_dx(psi0, dx))
        psi_t = sp.split_step_evolve(psi0, dx, dt=0.006, n_steps=450, v_x=v_x)
        rho = ff.density(psi_t)
        nrm = ff.norm_dx(psi_t, dx)
        self.assertAlmostEqual(nrm, 1.0, places=3)
        right = xs >= -1.0
        peaks = m.count_coarse_local_maxima(rho[right], stride=20)
        self.assertGreaterEqual(peaks, 8)
        self.assertLessEqual(peaks, 45)


if __name__ == "__main__":
    unittest.main()
