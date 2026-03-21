"""Sparse vs dense expm for 2D FD + slit H (needs SciPy)."""

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD_PATH = ROOT / "sim" / "schrodinger_2d_sparse_fd_expm_smoke.py"


def _have_scipy_sparse() -> bool:
    try:
        import scipy.sparse  # noqa: F401
        import scipy.sparse.linalg  # noqa: F401

        return True
    except ImportError:
        return False


def _load():
    spec = importlib.util.spec_from_file_location(
        "schrodinger_2d_sparse_fd_expm_smoke",
        MOD_PATH,
    )
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


@unittest.skipUnless(_have_scipy_sparse(), "scipy.sparse not installed")
class SparseFDExpmSmokeTests(unittest.TestCase):
    def test_matches_dense_small_grid(self) -> None:
        m = _load()
        d, n = m.sparse_vs_dense_expm_psi(nx=10, ny=10, t=0.08, v0=6.0)
        self.assertEqual(n, 100)
        self.assertLess(d, 1e-8)


if __name__ == "__main__":
    unittest.main()
