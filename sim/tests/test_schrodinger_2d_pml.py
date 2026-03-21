# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Tests for 2D PML boundary layer (optional NumPy)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PML_PATH = ROOT / "sim" / "schrodinger_2d_pml.py"
CORE_PATH = ROOT / "sim" / "schrodinger_2d_soft_double_slit.py"


def _have_numpy() -> bool:
    try:
        import numpy as _np  # noqa: F401

        return True
    except ImportError:
        return False


def _load_pml():
    spec = importlib.util.spec_from_file_location("schrodinger_2d_pml", PML_PATH)
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
class PMLMaskTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_mask_shape_1d(self) -> None:
        pml = _load_pml()
        mask = pml.pml_damping_mask_1d(64, 10, 5.0, 0.01, order=3)
        self.assertEqual(mask.shape, (64,))

    def test_mask_shape_2d(self) -> None:
        pml = _load_pml()
        mask = pml.pml_damping_mask_2d(64, 48, 10, 8, 5.0, 0.01, order=3)
        self.assertEqual(mask.shape, (64, 48))

    def test_mask_values_interior_one(self) -> None:
        """Interior (non-PML) cells should have mask value exactly 1."""
        np = self.np
        pml = _load_pml()
        n, n_pml = 64, 10
        mask = pml.pml_damping_mask_1d(n, n_pml, 5.0, 0.01, order=3)
        interior = mask[n_pml:-n_pml]
        np.testing.assert_allclose(interior, 1.0, atol=1e-15)

    def test_mask_values_boundary_less_than_one(self) -> None:
        """PML boundary cells should have mask < 1 (damping)."""
        pml = _load_pml()
        mask = pml.pml_damping_mask_1d(64, 10, 5.0, 0.01, order=3)
        self.assertLess(float(mask[0]), 1.0)
        self.assertLess(float(mask[-1]), 1.0)

    def test_mask_symmetry(self) -> None:
        """Mask should be symmetric: mask[j] == mask[n-1-j]."""
        np = self.np
        pml = _load_pml()
        mask = pml.pml_damping_mask_1d(64, 12, 5.0, 0.01, order=3)
        np.testing.assert_allclose(mask, mask[::-1], atol=1e-15)

    def test_zero_sigma_gives_unit_mask(self) -> None:
        """sigma_max=0 should produce all-ones mask."""
        np = self.np
        pml = _load_pml()
        mask = pml.pml_damping_mask_1d(64, 10, 0.0, 0.01, order=3)
        np.testing.assert_allclose(mask, 1.0, atol=1e-15)

    def test_zero_npml_gives_unit_mask(self) -> None:
        """n_pml=0 should produce all-ones mask."""
        np = self.np
        pml = _load_pml()
        mask = pml.pml_damping_mask_1d(64, 0, 5.0, 0.01, order=3)
        np.testing.assert_allclose(mask, 1.0, atol=1e-15)


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class PMLEvolutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_sigma_zero_recovers_plain(self) -> None:
        """PML with sigma_max=0 should reproduce plain split-step exactly."""
        np = self.np
        pml = _load_pml()
        m2 = _load_core()
        nx, ny = 64, 64
        lx, ly = 32.0, 32.0
        X, Y, dx, dy = m2.make_grid_2d(lx, ly, nx, ny)
        v_xy = np.zeros((nx, ny), dtype=float)
        psi0 = m2.initial_gaussian_2d(
            X, Y, x0=-6.0, y0=0.0, kx0=0.7, ky0=0.0, sigma0=0.9
        )
        psi0 = psi0 / np.sqrt(m2.norm_dxy(psi0, dx, dy))
        dt = 0.3 / 60
        steps = 60
        psi_pml = pml.split_step_evolve_2d_pml(
            psi0, dx, dy, dt, steps, v_xy,
            n_pml_x=10, n_pml_y=10, sigma_max=0.0,
        )
        psi_plain = m2.split_step_evolve_2d(
            psi0, dx, dy, dt=dt, n_steps=steps, v_xy=v_xy,
        )
        self.assertLess(float(np.max(np.abs(psi_pml - psi_plain))), 1e-9)

    def test_norm_decreases_at_boundary(self) -> None:
        """A packet hitting the PML boundary should lose norm."""
        np = self.np
        pml = _load_pml()
        m2 = _load_core()
        nx, ny = 80, 80
        lx, ly = 36.0, 36.0
        X, Y, dx, dy = m2.make_grid_2d(lx, ly, nx, ny)
        v_xy = np.zeros((nx, ny), dtype=float)
        xs_1d = X[:, 0]
        x_max = float(np.max(xs_1d))
        psi0 = m2.initial_gaussian_2d(
            X, Y, x0=x_max - 3.0, y0=0.0, kx0=1.5, ky0=0.0, sigma0=0.6
        )
        psi0 = psi0 / np.sqrt(m2.norm_dxy(psi0, dx, dy))
        dt = 0.5 / 100
        steps = 100
        psi_out = pml.split_step_evolve_2d_pml(
            psi0, dx, dy, dt, steps, v_xy,
            n_pml_x=16, n_pml_y=16, sigma_max=5.0, order=3,
        )
        n0 = m2.norm_dxy(psi0, dx, dy)
        n1 = m2.norm_dxy(psi_out, dx, dy)
        self.assertLess(n1, n0 - 1e-4)

    def test_pml_less_reflection_than_sponge(self) -> None:
        """PML should leave less interior residual than a simple sponge."""
        np = self.np
        pml = _load_pml()
        m2 = _load_core()
        nx, ny = 96, 96
        lx, ly = 40.0, 40.0
        X, Y, dx, dy = m2.make_grid_2d(lx, ly, nx, ny)
        v_xy = np.zeros((nx, ny), dtype=float)
        xs_1d = X[:, 0]
        x_max = float(np.max(xs_1d))
        psi0 = m2.initial_gaussian_2d(
            X, Y, x0=x_max - 6.0, y0=0.0, kx0=2.0, ky0=0.0, sigma0=1.0
        )
        psi0 = psi0 / np.sqrt(m2.norm_dxy(psi0, dx, dy))
        n_layer = 20
        dt = 1.5 / 300
        steps = 300

        # PML
        psi_pml = pml.split_step_evolve_2d_pml(
            psi0, dx, dy, dt, steps, v_xy,
            n_pml_x=n_layer, n_pml_y=n_layer, sigma_max=5.0, order=3,
        )
        # Sponge (cosine taper with eta=0.88)
        from pathlib import Path as _P
        import importlib.util as _iu

        _abs_path = _P(__file__).resolve().parents[2] / "sim" / "schrodinger_2d_absorbing_edges.py"
        _spec = _iu.spec_from_file_location("schrodinger_2d_absorbing_edges", _abs_path)
        _ab = _iu.module_from_spec(_spec)
        assert _spec and _spec.loader
        _spec.loader.exec_module(_ab)
        mask_sponge = _ab.absorption_mask_2d(nx, ny, n_layer, n_layer, 0.88)
        out_sponge = psi0.copy()
        for _ in range(steps):
            out_sponge = m2.kinetic_half_step_2d(out_sponge, dx, dy, dt=dt, mass=1.0)
            out_sponge = m2.potential_full_step(out_sponge, v_xy, dt)
            out_sponge = m2.kinetic_half_step_2d(out_sponge, dx, dy, dt=dt, mass=1.0)
            out_sponge *= mask_sponge

        # Compare interior residual
        s = slice(n_layer, -n_layer)
        rho_pml = float(np.sum(m2.density(psi_pml)[s, s]) * dx * dy)
        rho_sponge = float(np.sum(m2.density(out_sponge)[s, s]) * dx * dy)
        self.assertLess(rho_pml, rho_sponge)


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class ConductivityProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_profile_zero_outside_pml(self) -> None:
        np = self.np
        pml = _load_pml()
        x = np.linspace(0.0, 10.0, 100)
        sigma = pml.pml_conductivity_profile(x, x_pml=5.0, d_pml=5.0, sigma_max=10.0, order=3)
        np.testing.assert_allclose(sigma[x < 5.0], 0.0, atol=1e-15)

    def test_profile_max_at_boundary(self) -> None:
        np = self.np
        pml = _load_pml()
        x = np.array([10.0])
        sigma = pml.pml_conductivity_profile(x, x_pml=5.0, d_pml=5.0, sigma_max=10.0, order=3)
        np.testing.assert_allclose(sigma, 10.0, atol=1e-12)


if __name__ == "__main__":
    unittest.main()
