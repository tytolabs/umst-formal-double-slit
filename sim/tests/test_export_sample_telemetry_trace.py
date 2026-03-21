# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Golden-path: export_sample_telemetry_trace.py → telemetry_trace_consumer.py."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXPORT = ROOT / "sim" / "export_sample_telemetry_trace.py"
CONSUMER = ROOT / "sim" / "telemetry_trace_consumer.py"


class ExportSampleTelemetryTests(unittest.TestCase):
    def test_export_then_consume_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "trace.json"
            r1 = subprocess.run(
                [sys.executable, str(EXPORT), "--out", str(out)],
                cwd=str(ROOT),
                capture_output=True,
                text=True,
            )
            self.assertEqual(r1.returncode, 0, msg=r1.stderr + r1.stdout)
            self.assertTrue(out.is_file())

            r2 = subprocess.run(
                [sys.executable, str(CONSUMER), str(out), "--tolerance", "1e-8"],
                cwd=str(ROOT),
                capture_output=True,
                text=True,
            )
            self.assertEqual(r2.returncode, 0, msg=r2.stderr + r2.stdout)
            self.assertIn("0 failed", r2.stdout)


if __name__ == "__main__":
    unittest.main()
