# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Smoke-test toy script --plot when matplotlib is installed (CI); skip locally if missing."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "sim" / "toy_double_slit_mi_gate.py"


def _have_matplotlib() -> bool:
    try:
        import matplotlib.pyplot  # noqa: F401

        return True
    except ImportError:
        return False


@unittest.skipUnless(_have_matplotlib(), "matplotlib not installed")
class ToyMatplotlibPlotSmokeTests(unittest.TestCase):
    def test_plot_flag_writes_png(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            out_csv = tmp_path / "toy.csv"
            png_path = tmp_path / "complementarity_toy_plot.png"
            cmd = [
                sys.executable,
                str(SCRIPT),
                "--out",
                str(out_csv),
                "--validate",
                "--plot",
                "--info-steps",
                "5",
                "--x-steps",
                "8",
            ]
            subprocess.run(cmd, check=True)
            self.assertTrue(out_csv.is_file())
            self.assertTrue(png_path.is_file(), f"expected {png_path} from --plot")


if __name__ == "__main__":
    unittest.main()
