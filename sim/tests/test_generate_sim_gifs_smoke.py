# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Smoke test for scripts/generate_sim_gifs.py (--validate)."""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


def _import_ok(name: str) -> bool:
    try:
        __import__(name)
        return True
    except ImportError:
        return False


_DEPS = ("numpy", "matplotlib", "imageio")
_SKIP_MSG = "requires numpy, matplotlib, imageio"


@unittest.skipUnless(all(_import_ok(n) for n in _DEPS), _SKIP_MSG)
class TestGenerateSimGifsSmoke(unittest.TestCase):
    def test_validate_writes_gifs(self) -> None:
        root = Path(__file__).resolve().parents[2]
        script = root / "scripts" / "generate_sim_gifs.py"
        with tempfile.TemporaryDirectory() as tmp:
            env = {**os.environ, "TMPDIR": tmp}
            r = subprocess.run(
                [sys.executable, str(script), "--validate"],
                cwd=str(root),
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(r.returncode, 0, msg=r.stderr + r.stdout)
            self.assertTrue((Path(tmp) / "sim_1d_soft_slit.gif").is_file())
            self.assertTrue((Path(tmp) / "sim_2d_pml.gif").is_file())


if __name__ == "__main__":
    unittest.main()
