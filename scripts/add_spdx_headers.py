#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
"""
Idempotently add MIT SPDX + copyright headers to first-party sources under this repo.

Covers: Lean (.lean), Python (.py), Haskell (.hs), LaTeX (.tex), Markdown (.md),
Coq (.v), Agda (.agda).

Usage (from repo root):
  python3 scripts/add_spdx_headers.py
"""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]

LEAN_HEADER = """/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

"""

PY_HEADER_LINES = (
    "# SPDX-License-Identifier: MIT\n"
    "# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO\n"
    "\n"
)

HS_HEADER = (
    "-- SPDX-License-Identifier: MIT\n"
    "-- Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO\n"
    "\n"
)

TEX_HEADER = (
    "% SPDX-License-Identifier: MIT\n"
    "% Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO\n"
    "\n"
)

MD_HEADER = (
    "<!--\n"
    "SPDX-License-Identifier: MIT\n"
    "Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO\n"
    "-->\n"
    "\n"
)

COQ_HEADER = (
    "(* SPDX-License-Identifier: MIT *)\n"
    "(* Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO *)\n"
    "\n"
)

AGDA_HEADER = (
    "-- SPDX-License-Identifier: MIT\n"
    "-- Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO\n"
    "\n"
)


def _has_spdx_snippet(text: str, limit: int = 2000) -> bool:
    return "SPDX-License-Identifier: MIT" in text[:limit]


def _needs_lean(text: str) -> bool:
    return not _has_spdx_snippet(text, 1200)


def _patch_lean(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    if not _needs_lean(text):
        return False
    path.write_text(LEAN_HEADER + text, encoding="utf-8")
    return True


def _patch_py(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    if _has_spdx_snippet(text, 1500):
        return False
    lines = text.splitlines(keepends=True)
    if not lines:
        path.write_text(PY_HEADER_LINES, encoding="utf-8")
        return True
    if lines[0].startswith("#!"):
        path.write_text(lines[0] + PY_HEADER_LINES + "".join(lines[1:]), encoding="utf-8")
        return True
    path.write_text(PY_HEADER_LINES + text, encoding="utf-8")
    return True


def _patch_hs(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    if _has_spdx_snippet(text, 1200):
        return False
    path.write_text(HS_HEADER + text, encoding="utf-8")
    return True


def _patch_tex(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    if _has_spdx_snippet(text, 800):
        return False
    lines = text.splitlines(keepends=True)
    if lines and lines[0].lstrip().startswith("%!TEX"):
        path.write_text(lines[0] + TEX_HEADER + "".join(lines[1:]), encoding="utf-8")
        return True
    path.write_text(TEX_HEADER + text, encoding="utf-8")
    return True


def _patch_md(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    if _has_spdx_snippet(text, 1200):
        return False
    path.write_text(MD_HEADER + text, encoding="utf-8")
    return True


def _patch_coq(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    if _has_spdx_snippet(text, 1200):
        return False
    path.write_text(COQ_HEADER + text, encoding="utf-8")
    return True


def _patch_agda(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    if _has_spdx_snippet(text, 1500):
        return False
    path.write_text(AGDA_HEADER + text, encoding="utf-8")
    return True


def _skip_dir_parts(parts: tuple[str, ...]) -> bool:
    """Never touch tool caches, build outputs, or vendored trees."""
    skip = {
        ".lake",
        "__pycache__",
        ".pytest_cache",
        ".venv",
        "venv",
        "node_modules",
        "dist-newstyle",
        "dist",
        ".stack-work",
    }
    return bool(skip.intersection(parts))


def _rel_parts(path: Path) -> tuple[str, ...]:
    return path.relative_to(REPO_ROOT).parts


def main() -> int:
    lean_files = sorted(
        p
        for p in (REPO_ROOT / "Lean").rglob("*.lean")
        if not _skip_dir_parts(_rel_parts(p))
    )
    py_set = set((REPO_ROOT / "sim").rglob("*.py")) | set((REPO_ROOT / "scripts").rglob("*.py"))
    py_files = sorted(p for p in py_set if not _skip_dir_parts(_rel_parts(p)))
    hs_files = sorted(
        p for p in (REPO_ROOT / "Haskell").rglob("*.hs") if not _skip_dir_parts(_rel_parts(p))
    )
    tex_files = sorted(
        p for p in (REPO_ROOT / "Docs").glob("*.tex") if not _skip_dir_parts(_rel_parts(p))
    )
    md_files = sorted(
        p
        for p in REPO_ROOT.rglob("*.md")
        if not _skip_dir_parts(_rel_parts(p))
        # Plain-text LICENSE is not Markdown
        and p.name != "LICENSE.md"
    )
    coq_root = REPO_ROOT / "Coq"
    agda_root = REPO_ROOT / "Agda"
    coq_files = (
        sorted(
            p
            for p in coq_root.rglob("*.v")
            if coq_root.exists() and not _skip_dir_parts(_rel_parts(p))
        )
        if coq_root.is_dir()
        else []
    )
    agda_files = (
        sorted(
            p
            for p in agda_root.rglob("*.agda")
            if agda_root.exists() and not _skip_dir_parts(_rel_parts(p))
        )
        if agda_root.is_dir()
        else []
    )

    changed: list[Path] = []
    for p in lean_files:
        if _patch_lean(p):
            changed.append(p)
    for p in py_files:
        if _patch_py(p):
            changed.append(p)
    for p in hs_files:
        if _patch_hs(p):
            changed.append(p)
    for p in tex_files:
        if _patch_tex(p):
            changed.append(p)
    for p in md_files:
        if _patch_md(p):
            changed.append(p)
    for p in coq_files:
        if _patch_coq(p):
            changed.append(p)
    for p in agda_files:
        if _patch_agda(p):
            changed.append(p)

    for p in changed:
        print(f"updated: {p.relative_to(REPO_ROOT)}")
    print(f"done: {len(changed)} file(s) updated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
