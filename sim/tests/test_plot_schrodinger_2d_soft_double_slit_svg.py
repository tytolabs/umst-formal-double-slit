"""Tests for plot_schrodinger_2d_soft_double_slit_svg (stdlib)."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PLOT = ROOT / "sim" / "plot_schrodinger_2d_soft_double_slit_svg.py"


class PlotSchrodinger2DSoftDoubleSlitSvgTests(unittest.TestCase):
    def test_synthetic_csv_and_validate(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            csv_path = td_path / "g.csv"
            # 4 x 4 grid (>=16 rows for plotter), C order (x slow, y fast)
            xs = []
            ys = []
            for xi in [-1.0, 0.0, 1.0, 2.0]:
                for yj in [-2.0, -1.0, 0.0, 1.0]:
                    xs.append(xi)
                    ys.append(yj)
            with csv_path.open("w", encoding="utf-8", newline="") as f:
                f.write("x,y,rho\n")
                for x, y in zip(xs, ys):
                    r = (x + 2) * (y + 3) * 0.01
                    f.write(f"{x},{y},{r}\n")
            out_svg = td_path / "out.svg"
            r = subprocess.run(
                [
                    sys.executable,
                    str(PLOT),
                    "--in",
                    str(csv_path),
                    "--out",
                    str(out_svg),
                    "--validate",
                    "--stride",
                    "1",
                ],
                cwd=str(ROOT),
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(r.returncode, 0, msg=r.stderr)
            text = out_svg.read_text(encoding="utf-8")
            self.assertIn("heatmap", text)

    def test_repo_csv_if_present(self) -> None:
        csv_path = ROOT / "sim" / "out" / "schrodinger_2d_soft_double_slit_rho.csv"
        if not csv_path.is_file():
            self.skipTest("run schrodinger_2d_soft_double_slit.py first")
        with tempfile.TemporaryDirectory() as td:
            out_svg = Path(td) / "from_repo.svg"
            r = subprocess.run(
                [
                    sys.executable,
                    str(PLOT),
                    "--in",
                    str(csv_path),
                    "--out",
                    str(out_svg),
                    "--validate",
                    "--stride",
                    "2",
                ],
                cwd=str(ROOT),
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(r.returncode, 0, msg=r.stderr)
            self.assertIn("<svg", out_svg.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
