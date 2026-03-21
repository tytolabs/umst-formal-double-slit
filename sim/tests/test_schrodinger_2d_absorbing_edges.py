# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""2D absorbing sponge vs plain split-step (optional NumPy)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD_PATH = ROOT / "sim" / "schrodinger_2d_absorbing_edges.py"
CORE_PATH = ROOT / "sim" / "schrodinger_2d_soft_double_slit.py"


def _have_numpy() -> bool:
    try:
        import numpy as _np  # noqa: F401

        return True
    except ImportError:
        return False


def _load_abs():
    spec = importlib.util.spec_from_file_location("schrodinger_2d_absorbing_edges", MOD_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def _load_core():
    spec = importlib.util.spec_from_file_location("schrodinger_2d_soft_double_slit", CORE_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class Schrodinger2DAbsorbingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_zero_absorb_matches_plain(self) -> None:
        np = self.np
        a = _load_abs()
        m2 = _load_core()
        nx, ny = 64, 64
        lx, ly = 32.0, 32.0
        X, Y, dx, dy = m2.make_grid_2d(lx, ly, nx, ny)
        v_xy = m2.soft_double_slit_potential_2d(
            X,
            Y,
            v0=0.0,
            x_screen=0.0,
            slit_separation=1.0,
            slit_sigma=0.25,
        )
        psi0 = m2.initial_gaussian_2d(
            X, Y, x0=-6.0, y0=0.5, kx0=0.7, ky0=-0.1, sigma0=0.85
        )
        psi0 = psi0 / np.sqrt(m2.norm_dxy(psi0, dx, dy))
        mask0 = a.absorption_mask_2d(nx, ny, 0, 0, 0.9)
        dt = 0.3 / 60
        steps = 60
        pa = a.split_step_evolve_2d_with_absorption(
            psi0, dx, dy, dt=dt, n_steps=steps, v_xy=v_xy, mask=mask0
        )
        pb = m2.split_step_evolve_2d(
            psi0, dx, dy, dt=dt, n_steps=steps, v_xy=v_xy
        )
        self.assertLess(float(np.max(np.abs(pa - pb))), 1e-9)

    def test_corner_sponge_drops_norm(self) -> None:
        np = self.np
        a = _load_abs()
        m2 = _load_core()
        nx, ny = 80, 80
        lx, ly = 36.0, 36.0
        X, Y, dx, dy = m2.make_grid_2d(lx, ly, nx, ny)
        v_xy = np.zeros((nx, ny), dtype=float)
        xs_1d = X[:, 0]
        ys_1d = Y[0, :]
        x_max = float(np.max(xs_1d))
        y_max = float(np.max(ys_1d))
        psi0 = m2.initial_gaussian_2d(
            X,
            Y,
            x0=x_max - 1.4,
            y0=y_max - 1.4,
            kx0=0.5,
            ky0=0.4,
            sigma0=0.35,
        )
        psi0 = psi0 / np.sqrt(m2.norm_dxy(psi0, dx, dy))
        mask = a.absorption_mask_2d(nx, ny, 16, 16, 0.7)
        dt = 0.25 / 50
        steps = 50
        psi1 = a.split_step_evolve_2d_with_absorption(
            psi0, dx, dy, dt=dt, n_steps=steps, v_xy=v_xy, mask=mask
        )
        n0 = m2.norm_dxy(psi0, dx, dy)
        n1 = m2.norm_dxy(psi1, dx, dy)
        self.assertLess(n1, n0 - 1e-4)


if __name__ == "__main__":
    unittest.main()
