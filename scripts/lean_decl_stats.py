#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
Scan Lean sources (excluding `.lake`) and count declaration-like line starters.

Heuristic only — not a full Lean parser. Useful for PROOF-STATUS / release notes.
"""

from __future__ import annotations

import argparse
import re
from collections import Counter
from pathlib import Path
from typing import Iterable, List, Tuple

# Line-start patterns (after optional attributes / private / protected / noncomputable).
_PATTERNS: List[Tuple[str, re.Pattern[str]]] = [
    ("theorem", re.compile(r"^\s*(private\s+|protected\s+|noncomputable\s+)*theorem\s+\w")),
    ("lemma", re.compile(r"^\s*(private\s+|protected\s+|noncomputable\s+)*lemma\s+\w")),
    ("def", re.compile(r"^\s*(private\s+|protected\s+|noncomputable\s+)*def\s+\w")),
    ("abbrev", re.compile(r"^\s*(private\s+|protected\s+)*abbrev\s+\w")),
    ("instance", re.compile(r"^\s*(private\s+|protected\s+)*instance\s")),
    ("axiom", re.compile(r"^\s*axiom\s+\w")),
    ("opaque", re.compile(r"^\s*(private\s+|protected\s+)*opaque\s+\w")),
    ("inductive", re.compile(r"^\s*(private\s+|protected\s+)*inductive\s+\w")),
    ("structure", re.compile(r"^\s*(private\s+|protected\s+)*structure\s+\w")),
    ("class", re.compile(r"^\s*(private\s+|protected\s+)*class\s+\w")),
]


def _iter_lean_files(lean_root: Path) -> Iterable[Path]:
    skip = {".lake", "build"}
    for p in lean_root.rglob("*.lean"):
        if any(part in skip for part in p.parts):
            continue
        yield p


def _count_file(path: Path) -> Counter[str]:
    c: Counter[str] = Counter()
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return c
    for line in text.splitlines():
        s = line.strip()
        if not s or s.startswith("--"):
            continue
        for name, pat in _PATTERNS:
            if pat.match(line):
                c[name] += 1
                break
    return c


def scan(lean_root: Path) -> Tuple[Counter[str], int]:
    total: Counter[str] = Counter()
    nfiles = 0
    for f in sorted(_iter_lean_files(lean_root)):
        total.update(_count_file(f))
        nfiles += 1
    return total, nfiles


def main() -> None:
    p = argparse.ArgumentParser(description="Count Lean declaration-like lines (heuristic).")
    p.add_argument(
        "--lean-root",
        type=Path,
        default=None,
        help="Lean project root (default: ../Lean from this script)",
    )
    p.add_argument("--markdown", action="store_true", help="Print a short markdown bullet list.")
    args = p.parse_args()
    root = args.lean_root or Path(__file__).resolve().parent.parent / "Lean"
    if not root.is_dir():
        raise SystemExit(f"not a directory: {root}")

    counts, nfiles = scan(root)
    if args.markdown:
        root_resolved = root.resolve()
        cwd = Path.cwd().resolve()
        try:
            root_display = root_resolved.relative_to(cwd).as_posix()
        except ValueError:
            root_display = root_resolved.name
        print(f"- **Lean root:** `{root_display}`")
        print(f"- **`.lean` files scanned:** {nfiles} (`.lake` excluded)")
        for k in sorted(counts.keys()):
            print(f"- **`{k}` (line-start heuristic):** {counts[k]}")
        print(f"- **Sum of above kinds:** {sum(counts.values())}")
    else:
        print(f"Lean root: {root}")
        print(f"Files: {nfiles}")
        for k in sorted(counts.keys()):
            print(f"  {k}: {counts[k]}")
        print(f"  TOTAL: {sum(counts.values())}")


if __name__ == "__main__":
    main()
