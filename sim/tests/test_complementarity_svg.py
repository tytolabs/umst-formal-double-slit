# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PLOT = ROOT / "sim" / "plot_complementarity_svg.py"


class ComplementaritySvgTests(unittest.TestCase):
    def test_plot_writes_svg(self):
        csv_content = (
            "state,channel,pathWeight0,pathWeight1,fringeVisibility_V,"
            "whichPathDistinguishability_I,V_sq_plus_I_sq\n"
            "plus,identity,0.5,0.5,1.0,0.0,1.0\n"
            "plus,which_path,0.5,0.5,0.0,0.0,0.0\n"
        )
        with tempfile.TemporaryDirectory() as tmp:
            csv_path = Path(tmp) / "in.csv"
            out_path = Path(tmp) / "out.svg"
            csv_path.write_text(csv_content, encoding="utf-8")
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
            self.assertIn("xmlns", text)
            self.assertIn("Complementarity", text)


if __name__ == "__main__":
    unittest.main()
