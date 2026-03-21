import importlib.util
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "sim" / "qubit_kraus_sweep.py"


def _load_mod():
    name = "qubit_kraus_sweep"
    spec = importlib.util.spec_from_file_location(name, SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    # Python 3.9 dataclasses need the module present in sys.modules during class body.
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


class QubitKrausSweepTests(unittest.TestCase):
    def test_plus_identity_coherent(self):
        m = _load_mod()
        rho = m.kraus_apply(m.identity_kraus(), m.label_state("plus"))
        self.assertAlmostEqual(m.fringe_visibility(rho), 1.0, places=10)
        self.assertAlmostEqual(m.which_path_distinguishability(rho), 0.0, places=10)

    def test_plus_which_path_dephases(self):
        m = _load_mod()
        rho = m.kraus_apply(m.which_path_kraus(), m.label_state("plus"))
        self.assertAlmostEqual(m.fringe_visibility(rho), 0.0, places=10)
        self.assertAlmostEqual(m.which_path_distinguishability(rho), 0.0, places=10)
        self.assertAlmostEqual(m.path_weight(rho, 0), 0.5, places=10)
        self.assertAlmostEqual(m.path_weight(rho, 1), 0.5, places=10)

    def test_zero_which_path_orthogonal(self):
        m = _load_mod()
        rho = m.kraus_apply(m.which_path_kraus(), m.label_state("zero"))
        self.assertAlmostEqual(m.which_path_distinguishability(rho), 1.0, places=10)
        self.assertAlmostEqual(m.fringe_visibility(rho), 0.0, places=10)

    def test_complementarity_all_sweeps(self):
        m = _load_mod()
        tol = 1e-9
        for st in ("plus", "zero", "one"):
            rho0 = m.label_state(st)
            for ks in (m.identity_kraus(), m.which_path_kraus()):
                rho = m.kraus_apply(ks, rho0)
                comp = m.complementarity_sq(rho)
                self.assertLessEqual(comp, 1.0 + tol, msg=f"{st} comp={comp}")

    def test_script_validate_exit_zero(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "q.csv"
            subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT),
                    "--out",
                    str(out),
                    "--validate",
                ],
                check=True,
            )
            self.assertTrue(out.exists())


if __name__ == "__main__":
    unittest.main()
