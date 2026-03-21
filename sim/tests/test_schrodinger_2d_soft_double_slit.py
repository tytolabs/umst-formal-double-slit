"""2D split-step vs FFT2 and potential builder (optional NumPy)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD_PATH = ROOT / "sim" / "schrodinger_2d_soft_double_slit.py"


def _have_numpy() -> bool:
    try:
        import numpy as _np  # noqa: F401

        return True
    except ImportError:
        return False


def _load():
    spec = importlib.util.spec_from_file_location("schrodinger_2d_soft_double_slit", MOD_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class Schrodinger2DSoftDoubleSlitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_potential_shape_and_mask(self) -> None:
        np = self.np
        m = _load()
        X, Y, _, _ = m.make_grid_2d(20.0, 16.0, 32, 32)
        v = m.soft_double_slit_potential_2d(
            X,
            Y,
            v0=10.0,
            x_screen=0.0,
            slit_separation=1.0,
            slit_sigma=0.2,
        )
        self.assertEqual(v.shape, (32, 32))
        self.assertTrue(np.all(v[X < 0.0] == 0.0))
        self.assertGreater(float(np.max(v)), 0.0)

    def test_vzero_split_matches_fft2(self) -> None:
        np = self.np
        m = _load()
        X, Y, dx, dy = m.make_grid_2d(32.0, 32.0, 64, 64)
        psi0 = m.initial_gaussian_2d(X, Y, x0=-8.0, y0=0.2, kx0=0.9, ky0=-0.1, sigma0=0.9)
        psi0 = psi0 / np.sqrt(m.norm_dxy(psi0, dx, dy))
        v0 = np.zeros_like(X)
        t_total = 0.45
        n_steps = 90
        dt = t_total / n_steps
        psi_ss = m.split_step_evolve_2d(psi0, dx, dy, dt=dt, n_steps=n_steps, v_xy=v0)
        psi_ref = m.propagate_free_fft2(psi0, dx, dy, total_time=t_total)
        err = m.max_abs_rel_err(m.density(psi_ss), m.density(psi_ref))
        self.assertLess(err, 1e-5)
        self.assertAlmostEqual(m.norm_dxy(psi_ss, dx, dy), 1.0, places=5)

    def test_barrier_norm_smoke(self) -> None:
        np = self.np
        m = _load()
        X, Y, dx, dy = m.make_grid_2d(40.0, 40.0, 96, 96)
        psi0 = m.initial_gaussian_2d(X, Y, x0=-12.0, y0=0.0, kx0=1.1, ky0=0.0, sigma0=1.0)
        psi0 = psi0 / np.sqrt(m.norm_dxy(psi0, dx, dy))
        v_xy = m.soft_double_slit_potential_2d(
            X,
            Y,
            v0=18.0,
            x_screen=-3.0,
            slit_separation=1.4,
            slit_sigma=0.3,
        )
        psi1 = m.split_step_evolve_2d(psi0, dx, dy, dt=0.02, n_steps=100, v_xy=v_xy)
        self.assertAlmostEqual(m.norm_dxy(psi1, dx, dy), 1.0, places=3)


if __name__ == "__main__":
    unittest.main()
