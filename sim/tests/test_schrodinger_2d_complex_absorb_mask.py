# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Complex 2D edge mask vs real sponge when κ=0 (optional NumPy)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD_C = ROOT / "sim" / "schrodinger_2d_complex_absorb_mask.py"
MOD_R = ROOT / "sim" / "schrodinger_2d_absorbing_edges.py"
CORE_PATH = ROOT / "sim" / "schrodinger_2d_soft_double_slit.py"


def _have_numpy() -> bool:
    try:
        import numpy as _np  # noqa: F401

        return True
    except ImportError:
        return False


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class ComplexAbsorb2DTests(unittest.TestCase):
    def test_kappa_zero_matches_real_mask_and_evolution(self) -> None:
        import numpy as np

        c = _load("schrodinger_2d_complex_absorb_mask", MOD_C)
        r = _load("schrodinger_2d_absorbing_edges", MOD_R)
        m2 = _load("schrodinger_2d_soft_double_slit", CORE_PATH)
        nx, ny = 64, 64
        lx, ly = 32.0, 32.0
        X, Y, dx, dy = m2.make_grid_2d(lx, ly, nx, ny)
        v_xy = np.zeros((nx, ny), dtype=float)
        psi0 = m2.initial_gaussian_2d(
            X, Y, x0=-5.0, y0=0.3, kx0=0.6, ky0=-0.05, sigma0=0.8
        )
        psi0 = psi0 / np.sqrt(m2.norm_dxy(psi0, dx, dy))
        mr = r.absorption_mask_2d(nx, ny, 10, 12, 0.85)
        m0 = c.complex_absorption_mask_2d(nx, ny, 10, 12, 0.85, 0.0, 0.0)
        self.assertLess(float(np.max(np.abs(m0 - mr))), 1e-13)
        dt = 0.2 / 40
        steps = 40
        pa = c.split_step_evolve_2d_with_complex_mask(
            psi0, dx, dy, dt=dt, n_steps=steps, v_xy=v_xy, mask=m0
        )
        pb = r.split_step_evolve_2d_with_absorption(
            psi0, dx, dy, dt=dt, n_steps=steps, v_xy=v_xy, mask=mr
        )
        self.assertLess(float(np.max(np.abs(pa - pb))), 1e-9)

    def test_modulus_of_complex_mask_equals_real_sponge(self) -> None:
        import numpy as np

        c = _load("schrodinger_2d_complex_absorb_mask", MOD_C)
        r = _load("schrodinger_2d_absorbing_edges", MOD_R)
        nx, ny = 48, 56
        mr = r.absorption_mask_2d(nx, ny, 8, 9, 0.9)
        mc = c.complex_absorption_mask_2d(nx, ny, 8, 9, 0.9, 0.25, -0.18)
        self.assertLess(float(np.max(np.abs(np.abs(mc) - mr))), 1e-12)


if __name__ == "__main__":
    unittest.main()
