# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

import csv
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PLOT = ROOT / "sim" / "plot_schrodinger_absorbing_edges_svg.py"


class PlotSchrodingerAbsorbingEdgesSvgTests(unittest.TestCase):
    def test_plot_from_minimal_csv(self):
        with tempfile.TemporaryDirectory() as tmp:
            csv_path = Path(tmp) / "in.csv"
            out_path = Path(tmp) / "out.svg"
            with csv_path.open("w", encoding="utf-8", newline="") as f:
                f.write("x,rho\n")
                for i in range(16):
                    f.write(f"{-2.0 + 0.25 * i},{0.01 + 0.001 * (i % 4)}\n")
            subprocess.run(
                [sys.executable, str(PLOT), "--in", str(csv_path), "--out", str(out_path), "--validate"],
                check=True,
            )
            text = out_path.read_text(encoding="utf-8")
            self.assertIn("<svg", text)
            self.assertIn("absorbing edges", text)

    def test_plot_from_repo_csv_if_present(self):
        csv_path = ROOT / "sim" / "out" / "schrodinger_absorbing_edges_rho.csv"
        if not csv_path.is_file():
            self.skipTest("run schrodinger_1d_absorbing_edges.py first")
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
