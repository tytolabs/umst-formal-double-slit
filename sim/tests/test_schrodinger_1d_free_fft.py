"""NumPy FFT free propagation vs closed-form density (optional dep)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD_PATH = ROOT / "sim" / "schrodinger_1d_free_fft.py"


def _have_numpy() -> bool:
    try:
        import numpy as _np  # noqa: F401

        return True
    except ImportError:
        return False


def _load():
    spec = importlib.util.spec_from_file_location("schrodinger_1d_free_fft", MOD_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(_have_numpy(), "numpy not installed")
class Schrodinger1dFreeFftTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import numpy as np

        cls.np = np

    def test_norm_preserved(self) -> None:
        np = self.np
        m = _load()
        xs, dx = m.make_grid(32.0, 512)
        psi0 = m.initial_gaussian(xs, sigma0=0.9, k0=0.2)
        psi0 = psi0 / np.sqrt(m.norm_dx(psi0, dx))
        n0 = m.norm_dx(psi0, dx)
        psi1 = m.propagate_free_fft(psi0, dx, total_time=0.8)
        n1 = m.norm_dx(psi1, dx)
        self.assertAlmostEqual(n0, 1.0, places=5)
        self.assertAlmostEqual(n1, 1.0, places=4)

    def test_matches_closed_form_moderate(self) -> None:
        m = _load()
        nrm, err = m.run_case(length=48.0, n=4096, t=0.6, x0=0.0, k0=0.15, sigma0=1.0)
        self.assertAlmostEqual(nrm, 1.0, places=3)
        self.assertLess(err, 0.015)


if __name__ == "__main__":
    unittest.main()
