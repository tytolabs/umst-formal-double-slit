#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""One umst-formal pin for every language that takes it.

Lean takes umst-formal through Lake (Lean/lakefile.lean `require «umst-formal» … @ "<rev>"`, resolved in
Lean/lake-manifest.json); the Haskell suite `knowing-fibre-law` takes its executable second law (UMST.Process) through
cabal (Haskell/cabal.project `source-repository-package … tag: <rev>`). This check fails unless the three name the
same commit, so the second law the Haskell twins evaluate is the one the Lean proofs import.

Usage: python3 scripts/check_formal_pins.py
"""
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def read(path: str) -> str:
    return open(os.path.join(ROOT, path), encoding="utf-8").read()


def main() -> int:
    pins = {}
    m = re.search(r'require\s+«umst-formal»\s+from\s+git\s+"[^"]+"\s+@\s+"([0-9a-f]{40})"', read("Lean/lakefile.lean"))
    pins["Lean/lakefile.lean"] = m.group(1) if m else None
    manifest = json.loads(read("Lean/lake-manifest.json"))
    pins["Lean/lake-manifest.json"] = next((p["rev"] for p in manifest["packages"] if p["name"] in ("«umst-formal»", "umst-formal")), None)
    m = re.search(r"source-repository-package\s+type:\s*git\s+location:\s*\S*umst-formal(?:\.git)?\s+tag:\s*([0-9a-f]{40})",
                  read("Haskell/cabal.project"))
    pins["Haskell/cabal.project"] = m.group(1) if m else None
    missing = [k for k, v in pins.items() if v is None]
    if missing:
        print("FAIL: no umst-formal pin found in " + ", ".join(missing), file=sys.stderr)
        return 1
    if len(set(pins.values())) != 1:
        for k, v in pins.items():
            print(f"FAIL: {k} pins umst-formal at {v}", file=sys.stderr)
        return 1
    print(f"umst-formal pin {next(iter(pins.values()))[:7]}: Lean lakefile, Lake manifest and Haskell cabal.project agree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
