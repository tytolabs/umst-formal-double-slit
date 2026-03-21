import csv
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PLOT = ROOT / "sim" / "plot_toy_complementarity_svg.py"


class ToyComplementaritySvgTests(unittest.TestCase):
    def test_plot_from_minimal_csv(self):
        header = "info_I,visibility_V,V_sq_plus_I_sq,x,intensity,landauer_energy_j,temp_k\n"
        body = "\n".join(
            [
                "0.0,1.0,1.0,0.0,1.0,0.0,300.0",
                "0.5,0.8660254,1.0,0.0,0.5,0.0,300.0",
                "1.0,0.0,1.0,0.0,0.5,0.0,300.0",
            ]
        )
        with tempfile.TemporaryDirectory() as tmp:
            csv_path = Path(tmp) / "toy.csv"
            out_path = Path(tmp) / "out.svg"
            csv_path.write_text(header + body, encoding="utf-8")
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
            self.assertIn("Toy complementarity", text)


if __name__ == "__main__":
    unittest.main()
