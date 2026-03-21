# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Tests for 3D split-step Schrödinger (optional NumPy)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD_PATH = ROOT / "sim" / "schrodinger_3d_split_step.py"


def _have_numpy() -> bool:
    try:
        import numpy as _np  # noqa: F401

        return True
    except ImportError:
        return False


def _load_3d():
    spec = importlib.util.spec_from_file_location("schrodinger_3d_split_step", MOD_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class GridTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_grid_shape(self) -> None:
        m = _load_3d()
        X, Y, Z, dx, dy, dz = m.make_grid_3d(10.0, 12.0, 14.0, 16, 20, 24)
        self.assertEqual(X.shape, (16, 20, 24))
        self.assertEqual(Y.shape, (16, 20, 24))
        self.assertEqual(Z.shape, (16, 20, 24))

    def test_grid_spacing(self) -> None:
        np = self.np
        m = _load_3d()
        _, _, _, dx, dy, dz = m.make_grid_3d(10.0, 12.0, 14.0, 16, 20, 24)
        np.testing.assert_allclose(dx, 10.0 / 16, atol=1e-14)
        np.testing.assert_allclose(dy, 12.0 / 20, atol=1e-14)
        np.testing.assert_allclose(dz, 14.0 / 24, atol=1e-14)

    def test_grid_centred(self) -> None:
        np = self.np
        m = _load_3d()
        X, Y, Z, _, _, _ = m.make_grid_3d(10.0, 10.0, 10.0, 16, 16, 16)
        np.testing.assert_allclose(np.mean(X), 0.0, atol=1e-12)
        np.testing.assert_allclose(np.mean(Y), 0.0, atol=1e-12)
        np.testing.assert_allclose(np.mean(Z), 0.0, atol=1e-12)

    def test_grid_rejects_odd(self) -> None:
        m = _load_3d()
        with self.assertRaises(ValueError):
            m.make_grid_3d(10.0, 10.0, 10.0, 15, 16, 16)


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class GaussianTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_gaussian_normalization(self) -> None:
        np = self.np
        m = _load_3d()
        nx, ny, nz = 32, 32, 32
        lx, ly, lz = 20.0, 20.0, 20.0
        X, Y, Z, dx, dy, dz = m.make_grid_3d(lx, ly, lz, nx, ny, nz)
        psi = m.initial_gaussian_3d(X, Y, Z, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.5)
        nrm = m.norm_3d(psi, dx, dy, dz)
        # The analytic norm of our separable Gaussian should be close to 1
        # (may not be exact due to discretisation on a finite grid)
        np.testing.assert_allclose(nrm, 1.0, atol=0.05)

    def test_gaussian_is_complex(self) -> None:
        m = _load_3d()
        X, Y, Z, dx, dy, dz = m.make_grid_3d(10.0, 10.0, 10.0, 16, 16, 16)
        psi = m.initial_gaussian_3d(X, Y, Z, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 1.0)
        self.assertTrue(self.np.iscomplexobj(psi))


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class FreeEvolutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_free_norm_conservation(self) -> None:
        """Free evolution (V=0) should conserve norm to machine precision."""
        np = self.np
        m = _load_3d()
        nx, ny, nz = 16, 16, 16
        lx, ly, lz = 16.0, 16.0, 16.0
        X, Y, Z, dx, dy, dz = m.make_grid_3d(lx, ly, lz, nx, ny, nz)
        psi0 = m.initial_gaussian_3d(X, Y, Z, 0.0, 0.0, 0.0, 0.5, 0.0, 0.0, 1.5)
        psi0 = psi0 / np.sqrt(m.norm_3d(psi0, dx, dy, dz))
        v_zero = np.zeros((nx, ny, nz), dtype=float)
        dt = 0.2 / 40
        psi1 = m.split_step_evolve_3d(psi0, dx, dy, dz, dt, 40, v_zero)
        n0 = m.norm_3d(psi0, dx, dy, dz)
        n1 = m.norm_3d(psi1, dx, dy, dz)
        np.testing.assert_allclose(n1, n0, atol=1e-8)


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class PotentialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_potential_shape(self) -> None:
        m = _load_3d()
        nx, ny, nz = 16, 16, 16
        X, Y, Z, _, _, _ = m.make_grid_3d(16.0, 16.0, 16.0, nx, ny, nz)
        v = m.soft_double_slit_potential_3d(
            X, Y, Z, v0=10.0, x_screen=0.0,
            slit_separation=2.0, slit_sigma=0.5, screen_sigma=0.5,
        )
        self.assertEqual(v.shape, (nx, ny, nz))

    def test_potential_non_negative(self) -> None:
        np = self.np
        m = _load_3d()
        X, Y, Z, _, _, _ = m.make_grid_3d(16.0, 16.0, 16.0, 16, 16, 16)
        v = m.soft_double_slit_potential_3d(
            X, Y, Z, v0=10.0, x_screen=0.0,
            slit_separation=2.0, slit_sigma=0.5, screen_sigma=0.5,
        )
        self.assertTrue(np.all(v >= -1e-15))

    def test_potential_zero_when_v0_zero(self) -> None:
        np = self.np
        m = _load_3d()
        X, Y, Z, _, _, _ = m.make_grid_3d(16.0, 16.0, 16.0, 16, 16, 16)
        v = m.soft_double_slit_potential_3d(
            X, Y, Z, v0=0.0, x_screen=0.0,
            slit_separation=2.0, slit_sigma=0.5, screen_sigma=0.5,
        )
        np.testing.assert_allclose(v, 0.0, atol=1e-15)


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class AbsorptionMaskTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_mask_shape(self) -> None:
        m = _load_3d()
        mask = m.absorption_mask_3d(16, 20, 24, 4, 0.8)
        self.assertEqual(mask.shape, (16, 20, 24))

    def test_mask_interior_one(self) -> None:
        np = self.np
        m = _load_3d()
        n_abs = 4
        mask = m.absorption_mask_3d(32, 32, 32, n_abs, 0.8)
        interior = mask[n_abs:-n_abs, n_abs:-n_abs, n_abs:-n_abs]
        np.testing.assert_allclose(interior, 1.0, atol=1e-14)

    def test_zero_absorb_gives_ones(self) -> None:
        np = self.np
        m = _load_3d()
        mask = m.absorption_mask_3d(16, 16, 16, 0, 0.8)
        np.testing.assert_allclose(mask, 1.0, atol=1e-15)


if __name__ == "__main__":
    unittest.main()
