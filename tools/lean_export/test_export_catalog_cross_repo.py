#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""Tests for export_catalog.py cross-repo preview and merge gating."""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
EXPORT_SCRIPT = REPO_ROOT / "tools" / "lean_export" / "export_catalog.py"
FORMAL_LEAN = REPO_ROOT.parent / "umst-formal" / "Lean"

sys.path.insert(0, str(REPO_ROOT / "tools" / "lean_export"))
from export_catalog import (  # noqa: E402
    approve_cross_repo_merge,
    build_cross_repo_preview,
    build_merged_catalog,
    merge_catalog_modules,
)


class MergeHelpersTest(unittest.TestCase):
    def test_merge_tags_and_overlap_policy(self) -> None:
        primary = {
            "modules": [
                {"module": "UMST.DoubleSlit.Gate", "import_lines": []},
                {"module": "UMST.DoubleSlit.OnlyPrimary", "import_lines": []},
            ]
        }
        secondary = {
            "modules": [
                {"module": "UMST.Formal.Gate", "import_lines": []},
                {"module": "UMST.Formal.OnlySecondary", "import_lines": []},
            ]
        }
        merged = merge_catalog_modules(
            primary,
            secondary,
            primary_repo="ds",
            secondary_repo="uf",
        )
        self.assertEqual(len(merged), 3)
        repos = {m["module"]: m["repo"] for m in merged}
        self.assertEqual(repos["UMST.DoubleSlit.Gate"], "ds")
        self.assertEqual(repos["UMST.DoubleSlit.OnlyPrimary"], "ds")
        self.assertEqual(repos["UMST.Formal.OnlySecondary"], "uf")
        self.assertNotIn("UMST.Formal.Gate", repos)

    def test_preview_metadata_when_not_approved(self) -> None:
        primary = {"lean_root": "/a", "modules": [{"module": "A.X"}], "digest": "aa"}
        secondary = {"lean_root": "/b", "modules": [{"module": "B.Y"}], "digest": "bb"}
        preview = build_cross_repo_preview(
            primary,
            secondary,
            primary_repo="ds",
            secondary_repo="uf",
            approved=False,
        )
        self.assertTrue(preview["dry_run"])
        self.assertTrue(preview["merge_blocked"])
        self.assertFalse(preview["approve_cross_repo_merge_set"])
        self.assertEqual(len(preview["modules"]), 2)
        self.assertTrue(all("repo" in m for m in preview["modules"]))
        self.assertIn("merged_digest_hex", preview)

    def test_preview_always_dry_run_even_when_approved(self) -> None:
        """Preview file is never SSOT; dry_run must not flip false when APPROVE=1."""
        primary = {"lean_root": "/a", "modules": [{"module": "A.X"}], "digest": "aa"}
        secondary = {"lean_root": "/b", "modules": [{"module": "B.Y"}], "digest": "bb"}
        preview = build_cross_repo_preview(
            primary,
            secondary,
            primary_repo="ds",
            secondary_repo="uf",
            approved=True,
        )
        self.assertTrue(preview["dry_run"])
        self.assertFalse(preview["merge_blocked"])
        self.assertTrue(preview["approve_cross_repo_merge_set"])

    def test_merged_catalog_digest_stable(self) -> None:
        primary = {"lean_root": "/a", "modules": [{"module": "A.X", "import_lines": []}], "digest": "x"}
        secondary = {"lean_root": "/b", "modules": [{"module": "B.Y", "import_lines": []}], "digest": "y"}
        merged = build_merged_catalog(primary, secondary, primary_repo="ds", secondary_repo="uf")
        self.assertTrue(merged["cross_repo_merge"])
        self.assertEqual(len(merged["modules"]), 2)
        self.assertRegex(merged["digest"], r"^[0-9a-f]{64}$")


class CrossRepoCliTest(unittest.TestCase):
    @unittest.skipUnless(FORMAL_LEAN.is_dir(), "umst-formal/Lean not present")
    def test_cross_repo_only_skips_canonical_catalog(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            preview_out = tmp_path / "preview.json"
            catalog_out = tmp_path / "catalog.json"
            env = {**os.environ}
            env.pop("APPROVE_CROSS_REPO_MERGE", None)

            subprocess.run(
                [
                    sys.executable,
                    str(EXPORT_SCRIPT),
                    "--lean-root",
                    str(REPO_ROOT / "Lean"),
                    "--also-lean-root",
                    str(FORMAL_LEAN),
                    "--also-lean-repo-tag",
                    "umst-formal",
                    "--cross-repo-only",
                    "--cross-repo-preview-out",
                    str(preview_out),
                    "--out",
                    str(catalog_out),
                ],
                cwd=REPO_ROOT,
                check=True,
                env=env,
            )

            self.assertTrue(preview_out.is_file())
            self.assertFalse(catalog_out.exists())
            preview = json.loads(preview_out.read_text(encoding="utf-8"))
            self.assertTrue(preview.get("dry_run"))
            self.assertTrue(preview.get("merge_blocked"))
            self.assertEqual(preview.get("role"), "lean_catalog_cross_repo_preview")
            modules = preview.get("modules", [])
            self.assertGreater(len(modules), 0)
            self.assertTrue(all("repo" in m for m in modules))

    @unittest.skipUnless(FORMAL_LEAN.is_dir(), "umst-formal/Lean not present")
    def test_cross_repo_only_dry_run_with_approve_env(self) -> None:
        """APPROVE_CROSS_REPO_MERGE=1 must not mark preview JSON as non-dry-run."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            preview_out = tmp_path / "preview.json"
            env = {**os.environ, "APPROVE_CROSS_REPO_MERGE": "1"}

            subprocess.run(
                [
                    sys.executable,
                    str(EXPORT_SCRIPT),
                    "--lean-root",
                    str(REPO_ROOT / "Lean"),
                    "--also-lean-root",
                    str(FORMAL_LEAN),
                    "--also-lean-repo-tag",
                    "umst-formal",
                    "--cross-repo-only",
                    "--cross-repo-preview-out",
                    str(preview_out),
                ],
                cwd=REPO_ROOT,
                check=True,
                env=env,
            )

            preview = json.loads(preview_out.read_text(encoding="utf-8"))
            self.assertTrue(preview.get("dry_run"))
            self.assertTrue(preview.get("approve_cross_repo_merge_set"))

    def test_approve_env_gate(self) -> None:
        with mock.patch.dict(os.environ, {}, clear=True):
            self.assertFalse(approve_cross_repo_merge())
        with mock.patch.dict(os.environ, {"APPROVE_CROSS_REPO_MERGE": "1"}, clear=True):
            self.assertTrue(approve_cross_repo_merge())


if __name__ == "__main__":
    unittest.main()
