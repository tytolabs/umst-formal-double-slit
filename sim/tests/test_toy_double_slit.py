import csv
import importlib.util
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "sim" / "toy_double_slit_mi_gate.py"


def _load_sim_module():
    spec = importlib.util.spec_from_file_location("toy_double_slit_mi_gate", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(module)
    return module


class ToyDoubleSlitTests(unittest.TestCase):
    def test_visibility_complementarity_bound(self):
        sim_mod = _load_sim_module()

        for i in range(0, 101):
            info = i / 100.0
            vis = sim_mod.visibility_from_info(info)
            self.assertGreaterEqual(vis, 0.0)
            self.assertLessEqual(vis, 1.0)
            self.assertLessEqual(vis * vis + info * info, 1.0 + 1e-12)

    def test_intensity_bounds(self):
        sim_mod = _load_sim_module()

        for vis in (0.0, 0.25, 0.5, 0.75, 1.0):
            for i in range(0, 101):
                x = i / 100.0
                intensity = sim_mod.fringe_intensity(x, vis)
                self.assertGreaterEqual(intensity, -1e-12)
                self.assertLessEqual(intensity, 1.0 + 1e-12)

    def test_landauer_nonnegative(self):
        sim_mod = _load_sim_module()

        for bits in (0.0, 0.1, 0.5, 1.0):
            energy = sim_mod.landauer_energy(bits, 300.0)
            self.assertGreaterEqual(energy, 0.0)

    def test_script_generates_expected_columns(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            out_csv = Path(tmpdir) / "toy.csv"
            summary_csv = Path(tmpdir) / "summary.csv"
            cmd = [
                sys.executable,
                str(SCRIPT),
                "--out",
                str(out_csv),
                "--summary-csv",
                str(summary_csv),
                "--validate",
            ]
            subprocess.run(cmd, check=True)
            self.assertTrue(out_csv.exists())
            self.assertTrue(summary_csv.exists())

            with out_csv.open("r", encoding="utf-8", newline="") as f:
                reader = csv.DictReader(f)
                first = next(reader)
                self.assertIn("V_sq_plus_I_sq", first)
                self.assertIn("temp_k", first)


if __name__ == "__main__":
    unittest.main()
