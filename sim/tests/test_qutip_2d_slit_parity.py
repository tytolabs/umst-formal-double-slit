# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""QuTiP vs scipy on 2D FD Hamiltonian + soft slit potential (optional QuTiP)."""

import importlib.util
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD_PATH = ROOT / "sim" / "qutip_schrodinger_2d_slit_parity.py"


def _have_qutip() -> bool:
    try:
        import qutip  # noqa: F401

        return True
    except ImportError:
        return False


def _load():
    spec = importlib.util.spec_from_file_location("qutip_schrodinger_2d_slit_parity", MOD_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    sys.modules["qutip_schrodinger_2d_slit_parity"] = mod
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(_have_qutip(), "qutip not installed")
class QuTiP2DSlitParityTests(unittest.TestCase):
    def test_sesolve_matches_scipy_with_slit(self) -> None:
        m = _load()
        d, _nrm = m.run_slit_parity(nx=12, ny=10, t=0.2, v0=12.0)
        self.assertLess(d, 1e-5)

    def test_diagnostic_gap_is_finite(self) -> None:
        m = _load()
        g = m.split_step_vs_fd_density_gap(nx=14, ny=14, t=0.15, n_steps=30)
        self.assertGreaterEqual(g, 0.0)
        self.assertTrue(g == g)


if __name__ == "__main__":
    unittest.main()
