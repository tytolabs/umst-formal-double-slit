# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PLOT = ROOT / "sim" / "plot_classical_double_slit_svg.py"


class PlotClassicalDoubleSlitSvgTests(unittest.TestCase):
    def test_plot_computed_curve_validate(self):
        with tempfile.TemporaryDirectory() as tmp:
            out_path = Path(tmp) / "out.svg"
            subprocess.run(
                [
                    sys.executable,
                    str(PLOT),
                    "--out",
                    str(out_path),
                    "--validate",
                    "--points",
                    "401",
                    "--sin-max",
                    "0.015",
                ],
                check=True,
            )
            text = out_path.read_text(encoding="utf-8")
            self.assertIn("<svg", text)
            self.assertIn("Fraunhofer", text)

    def test_plot_from_csv(self):
        csv_path = ROOT / "sim" / "out" / "classical_double_slit_far_field.csv"
        if not csv_path.is_file():
            self.skipTest("run classical_double_slit_far_field.py once to generate CSV")
        with tempfile.TemporaryDirectory() as tmp:
            out_path = Path(tmp) / "from_csv.svg"
            subprocess.run(
                [
                    sys.executable,
                    str(PLOT),
                    "--in",
                    str(csv_path),
                    "--out",
                    str(out_path),
                    "--validate",
                ],
                check=True,
            )
            self.assertIn("<svg", out_path.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
