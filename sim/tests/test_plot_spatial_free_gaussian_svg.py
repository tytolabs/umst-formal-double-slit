import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PLOT = ROOT / "sim" / "plot_spatial_free_gaussian_svg.py"


class PlotSpatialFreeGaussianSvgTests(unittest.TestCase):
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
                    "--half-width",
                    "16",
                    "--t",
                    "0.5",
                ],
                check=True,
            )
            text = out_path.read_text(encoding="utf-8")
            self.assertIn("<svg", text)
            self.assertIn("Gaussian", text)

    def test_plot_from_csv(self):
        csv_path = ROOT / "sim" / "out" / "spatial_free_gaussian.csv"
        if not csv_path.is_file():
            self.skipTest("run spatial_free_gaussian_1d.py once to generate CSV")
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
