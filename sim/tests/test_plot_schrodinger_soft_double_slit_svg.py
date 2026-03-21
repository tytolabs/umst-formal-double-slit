# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

import csv
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PLOT = ROOT / "sim" / "plot_schrodinger_soft_double_slit_svg.py"


class PlotSchrodingerSoftDoubleSlitSvgTests(unittest.TestCase):
    def test_plot_from_minimal_csv(self):
        rows = []
        for i in range(20):
            x = -5.0 + 0.5 * i
            v = 10.0 * max(0.0, 1.0 - abs(x) * 0.15)
            rho = 0.05 + 0.02 * (i % 3)
            rows.append((x, v, rho))
        with tempfile.TemporaryDirectory() as tmp:
            csv_path = Path(tmp) / "in.csv"
            out_path = Path(tmp) / "out.svg"
            with csv_path.open("w", encoding="utf-8", newline="") as f:
                f.write("x,V,rho\n")
                for x, v, rho in rows:
                    f.write(f"{x},{v},{rho}\n")
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
            text = out_path.read_text(encoding="utf-8")
            self.assertIn("<svg", text)
            self.assertIn("Soft double-slit", text)

    def test_plot_from_repo_csv_if_present(self):
        csv_path = ROOT / "sim" / "out" / "schrodinger_soft_double_slit_rho.csv"
        if not csv_path.is_file():
            self.skipTest("run schrodinger_1d_soft_double_slit.py first")
        with tempfile.TemporaryDirectory() as tmp:
            out_path = Path(tmp) / "from_repo.svg"
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
