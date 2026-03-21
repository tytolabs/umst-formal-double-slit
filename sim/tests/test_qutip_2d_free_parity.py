"""QuTiP vs scipy expm for 2D periodic free Hamiltonian (optional QuTiP)."""

import importlib.util
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD_PATH = ROOT / "sim" / "qutip_schrodinger_2d_free_parity.py"


def _have_qutip() -> bool:
    try:
        import qutip  # noqa: F401

        return True
    except ImportError:
        return False


def _load():
    spec = importlib.util.spec_from_file_location("qutip_schrodinger_2d_free_parity", MOD_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    sys.modules["qutip_schrodinger_2d_free_parity"] = mod
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(_have_qutip(), "qutip not installed")
class QuTiP2DFreeParityTests(unittest.TestCase):
    def test_sesolve_matches_scipy_expm(self) -> None:
        m = _load()
        d, _nrm = m.run_parity(nx=12, ny=10, t=0.28, mass=1.0)
        self.assertLess(d, 1e-5)

    def test_spectral_fd_gap_is_finite(self) -> None:
        """Diagnostic: FFT vs FD densities differ; ensure function runs."""
        m = _load()
        g = m.spectral_vs_fd_gap(nx=14, ny=14, t=0.2)
        self.assertGreaterEqual(g, 0.0)
        self.assertTrue(g == g)  # not NaN


if __name__ == "__main__":
    unittest.main()
