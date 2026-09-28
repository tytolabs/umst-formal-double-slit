#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
"""
Inventory formal trust gaps for umst-formal-double-slit (P0-13 / FORMAL-GAPS gate).

Comment-stripped line scan — not a full parser. Emits workspace/ops/analysis/formal/FORMAL_GAPS.json
when run with --emit, or validates an existing inventory with --check.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

REPO_ROOT = Path(__file__).resolve().parents[3]
DS_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = REPO_ROOT / "workspace" / "ops" / "analysis" / "formal" / "FORMAL_GAPS.json"

_NATIVE_DECIDE = re.compile(r"\bnative_decide\b")
_COQ_AXIOM = re.compile(r"^\s*Axiom\s+(\w+)")
_COQ_PARAMETER = re.compile(r"^\s*Parameter\s+(\w+)")
_AGDA_POSTULATE = re.compile(r"^\s*postulate\b")


def _strip_line_comment(line: str, lang: str) -> str:
    if lang == "lean":
        if line.strip().startswith("--"):
            return ""
        return line.split("--", 1)[0]
    if lang in ("coq", "v"):
        return line.split("(*", 1)[0]
    if lang == "agda":
        if line.strip().startswith("--"):
            return ""
        return line.split("--", 1)[0]
    return line


def _iter_sources(root: Path, suffix: str, skip: Iterable[str]) -> Iterable[Path]:
    skip_set = set(skip)
    for p in sorted(root.rglob(f"*{suffix}")):
        if any(part in skip_set for part in p.parts):
            continue
        yield p


def _classify_native_decide(rel: str, line_no: int, context: str) -> Tuple[str, str]:
    ctx = context.strip()
    name_match = re.search(
        r"(theorem|lemma|def)\s+(\w+)|(\w+)\s*=\s*true\s*:=",
        ctx,
    )
    name = ""
    if name_match:
        name = name_match.group(2) or name_match.group(3) or ""
    lower = (name + " " + ctx).lower()
    if "latticescaffold" in lower.replace("_", ""):
        return (
            "trust_extension_lattice_scaffold",
            "Finite ChemConstants scaffold equality; kernel reduction via native_decide until Decidable instance lands.",
        )
    if "conservationhonest" in lower.replace("_", ""):
        return (
            "trust_extension_conservation_honest",
            "Registry row conservation checked by compiler reduction on closed boolean certificate.",
        )
    if "conservationaxiom" in lower.replace("_", ""):
        return (
            "trust_extension_conservation_axiom",
            "Axiom-shaped conservation flag materialized as native_decide certificate pending proof refactor.",
        )
    if "every_z_in" in lower or "iupac" in lower:
        return (
            "trust_extension_table_census",
            "Periodic-table membership census; feasible with decide after finset enumeration.",
        )
    return (
        "trust_extension_native_decide",
        "Lean.ofReduceBool trust extension; keep listed until replaced by decide/norm_num or Decidable proof.",
    )


def _scan_lean_native_decide(lean_root: Path) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for path in _iter_sources(lean_root, ".lean", (".lake", "build")):
        rel = path.relative_to(REPO_ROOT).as_posix()
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        for i, raw in enumerate(lines, start=1):
            line = _strip_line_comment(raw, "lean")
            if not _NATIVE_DECIDE.search(line):
                continue
            ctx = line
            if "theorem" not in ctx and "lemma" not in ctx:
                for j in range(max(0, i - 4), min(len(lines), i + 1)):
                    ctx = lines[j] + " " + ctx
            kind, reason = _classify_native_decide(rel, i, ctx)
            rows.append(
                {
                    "path": rel,
                    "line": i,
                    "kind": kind,
                    "reason": reason,
                    "snippet": line.strip()[:240],
                }
            )
    return rows


def _scan_coq(coq_root: Path) -> Dict[str, Any]:
    axioms: List[Dict[str, str]] = []
    parameters: List[Dict[str, str]] = []
    for path in _iter_sources(coq_root, ".v", (".coq-native",)):
        rel = path.relative_to(REPO_ROOT).as_posix()
        for i, raw in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), start=1):
            line = _strip_line_comment(raw, "coq")
            m = _COQ_AXIOM.match(line)
            if m:
                axioms.append({"path": rel, "line": str(i), "name": m.group(1)})
            m = _COQ_PARAMETER.match(line)
            if m:
                parameters.append({"path": rel, "line": str(i), "name": m.group(1)})
    return {
        "axiom_count": len(axioms),
        "parameter_count": len(parameters),
        "axioms": axioms,
        "parameters": parameters,
    }


def _scan_agda(agda_root: Path) -> Dict[str, Any]:
    blocks: List[Dict[str, Any]] = []
    for path in _iter_sources(agda_root, ".agda", (".agda-lib",)):
        rel = path.relative_to(REPO_ROOT).as_posix()
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        i = 0
        while i < len(lines):
            line = _strip_line_comment(lines[i], "agda")
            if _AGDA_POSTULATE.match(line):
                start = i + 1
                names: List[str] = []
                j = i + 1
                while j < len(lines):
                    chunk = _strip_line_comment(lines[j], "agda").strip()
                    if not chunk:
                        j += 1
                        continue
                    if chunk.startswith("postulate"):
                        break
                    if chunk.startswith("module ") or chunk.startswith("record ") or chunk.startswith("data "):
                        break
                    nm = re.match(r"(\S+)\s*:", chunk)
                    if nm:
                        names.append(nm.group(1))
                    j += 1
                blocks.append({"path": rel, "line": start, "names": names})
            i += 1
    return {
        "postulate_block_count": len(blocks),
        "blocks": blocks,
    }


def build_inventory() -> Dict[str, Any]:
    lean_root = DS_ROOT / "Lean"
    coq_root = DS_ROOT / "Coq"
    agda_root = DS_ROOT / "Agda"
    native = _scan_lean_native_decide(lean_root)
    coq = _scan_coq(coq_root)
    agda = _scan_agda(agda_root)
    return {
        "schema": "formal_gaps_v1",
        "project": "umst-formal-double-slit",
        "generated_at": datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
        "physics_green": False,
        "census": {
            "coq_axioms": coq["axiom_count"],
            "coq_parameters": coq["parameter_count"],
            "agda_postulate_blocks": agda["postulate_block_count"],
            "lean_native_decide_sites": len(native),
        },
        "coq": coq,
        "agda": agda,
        "lean_native_decide": native,
        "non_claim": "Inventory only — listed gaps remain trust extensions until replaced; physics_green false",
    }


def _load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _check_live(inv: Dict[str, Any]) -> None:
    live = build_inventory()
    c_live = live["census"]
    c_inv = inv["census"]
    for key in c_live:
        if c_live[key] != c_inv.get(key):
            raise SystemExit(
                f"census mismatch on {key}: live={c_live[key]} inventory={c_inv.get(key)}"
            )
    if len(inv.get("lean_native_decide", [])) != c_live["lean_native_decide_sites"]:
        raise SystemExit("lean_native_decide row count stale")


def main() -> None:
    ap = argparse.ArgumentParser(description="Formal gaps inventory for double-slit mirrors.")
    ap.add_argument("--emit", type=Path, default=None, help=f"Write JSON (default: {DEFAULT_OUT})")
    ap.add_argument("--check", type=Path, default=None, help="Verify inventory matches live scan")
    ap.add_argument("--stdout", action="store_true", help="Print JSON to stdout")
    args = ap.parse_args()

    inv = build_inventory()
    if args.check:
        _check_live(_load_json(args.check))
        print("formal_gaps: check OK")
        return
    out = args.emit or DEFAULT_OUT
    if args.stdout:
        print(json.dumps(inv, indent=2))
        return
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(inv, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {out} ({inv['census']['lean_native_decide_sites']} native_decide sites)")


if __name__ == "__main__":
    main()
