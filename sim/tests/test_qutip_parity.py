# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

import unittest

from pathlib import Path
import importlib.util
import sys

ROOT = Path(__file__).resolve().parents[2]
QUTIP_MOD = ROOT / "sim" / "qutip_qubit_kraus.py"
STDLIB_MOD = ROOT / "sim" / "qubit_kraus_sweep.py"


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def _have_qutip() -> bool:
    try:
        import qutip  # noqa: F401

        return True
    except ImportError:
        return False


@unittest.skipUnless(_have_qutip(), "qutip not installed")
class QuTiPParityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.qt = _load("qutip_qubit_kraus", QUTIP_MOD)
        cls.st = _load("qubit_kraus_sweep", STDLIB_MOD)

    def test_sweep_matches_stdlib(self):
        states = ("plus", "zero", "one")
        channels = (
            ("identity", self.qt.apply_identity, self.st.identity_kraus()),
            ("which_path", self.qt.apply_which_path, self.st.which_path_kraus()),
        )
        eps = 1e-8
        for st in states:
            rho_q = self.qt.label_state(st)
            rho_s = self.st.label_state(st)
            for _name, q_apply, ks in channels:
                rq = q_apply(rho_q)
                rs = self.st.kraus_apply(ks, rho_s)
                pq0, pq1, vq, iq = self.qt.metrics_from_qobj(rq)
                ps0 = self.st.path_weight(rs, 0)
                ps1 = self.st.path_weight(rs, 1)
                vs = self.st.fringe_visibility(rs)
                is_ = self.st.which_path_distinguishability(rs)
                self.assertAlmostEqual(pq0, ps0, places=7)
                self.assertAlmostEqual(pq1, ps1, places=7)
                self.assertLessEqual(abs(vq - vs), eps)
                self.assertLessEqual(abs(iq - is_), eps)


if __name__ == "__main__":
    unittest.main()
