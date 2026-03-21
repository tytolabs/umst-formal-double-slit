"""Smoke-test toy script --generate-gif when matplotlib + imageio are installed (CI); skip otherwise."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "sim" / "toy_double_slit_mi_gate.py"


def _have_gif_stack() -> bool:
    try:
        import matplotlib.pyplot  # noqa: F401
        import imageio.v2 as imageio  # noqa: F401

        return True
    except ImportError:
        return False


@unittest.skipUnless(_have_gif_stack(), "matplotlib and imageio required for GIF")
class ToyGifSmokeTests(unittest.TestCase):
    def test_generate_gif_writes_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            out_csv = tmp_path / "toy.csv"
            gif_path = tmp_path / "interference_collapse.gif"
            cmd = [
                sys.executable,
                str(SCRIPT),
                "--out",
                str(out_csv),
                "--validate",
                "--generate-gif",
                "--info-steps",
                "4",
                "--x-steps",
                "10",
            ]
            subprocess.run(cmd, check=True, timeout=120)
            self.assertTrue(out_csv.is_file())
            self.assertTrue(gif_path.is_file(), f"expected {gif_path}")


if __name__ == "__main__":
    unittest.main()
