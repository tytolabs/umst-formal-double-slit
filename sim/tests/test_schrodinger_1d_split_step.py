# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Split-step vs free FFT (optional NumPy)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD_PATH = ROOT / "sim" / "schrodinger_1d_split_step.py"
FFT_PATH = ROOT / "sim" / "schrodinger_1d_free_fft.py"


def _have_numpy() -> bool:
    try:
        import numpy as _np  # noqa: F401

        return True
    except ImportError:
        return False


def _load_split():
    spec = importlib.util.spec_from_file_location("schrodinger_1d_split_step", MOD_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def _load_fft():
    spec = importlib.util.spec_from_file_location("schrodinger_1d_free_fft", FFT_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class SplitStepTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_vzero_matches_fft(self) -> None:
        np = self.np
        sp = _load_split()
        ff = _load_fft()
        xs, dx = ff.make_grid(36.0, 1024)
        psi0 = ff.initial_gaussian(xs, x0=-5.0, k0=0.8, sigma0=0.85)
        psi0 = psi0 / np.sqrt(ff.norm_dx(psi0, dx))
        v0 = np.zeros_like(xs)
        t_total = 0.7
        n_steps = 140
        dt = t_total / n_steps
        psi_ss = sp.split_step_evolve(psi0, dx, dt=dt, n_steps=n_steps, v_x=v0)
        psi_fft = ff.propagate_free_fft(psi0, dx, total_time=t_total)
        err = ff.max_abs_rel_err(ff.density(psi_ss), ff.density(psi_fft))
        self.assertLess(err, 1e-6)
        self.assertAlmostEqual(ff.norm_dx(psi_ss, dx), 1.0, places=5)

    def test_barrier_unitary_norm(self) -> None:
        np = self.np
        sp = _load_split()
        ff = _load_fft()
        xs, dx = ff.make_grid(48.0, 2048)
        psi0 = ff.initial_gaussian(xs, x0=-10.0, k0=1.0, sigma0=1.0)
        psi0 = psi0 / np.sqrt(ff.norm_dx(psi0, dx))
        v_x = sp.gaussian_barrier(xs, v0=12.0, xb=0.0, width=0.5)
        psi1 = sp.split_step_evolve(psi0, dx, dt=0.04, n_steps=100, v_x=v_x)
        self.assertAlmostEqual(ff.norm_dx(psi1, dx), 1.0, places=4)


if __name__ == "__main__":
    unittest.main()
