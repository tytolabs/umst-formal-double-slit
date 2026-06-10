#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
"""
Emit a UMST Lean catalog artifact (minimal viable digest + import graph skeleton).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
from pathlib import Path
from typing import Any, Dict, List

APPROVE_CROSS_REPO_MERGE_ENV = "APPROVE_CROSS_REPO_MERGE"


DECL_RE = re.compile(
    r"^\s*(theorem|lemma|axiom|def|instance|inductive|structure|class)\s+([^\s:]+)",
    re.MULTILINE,
)
IMPORT_RE = re.compile(r"""^\s*import\s+(?:«[^»]+»|[A-Za-z0-9_.]+)(?:\.(?:«[^»]+»|[A-Za-z0-9_.]+))*""")



ROOT_PREFIX = "UMST.DoubleSlit"
ROOTS_ASSIGN_RE = re.compile(r"roots\s*:=\s*#\[", re.MULTILINE)


def parse_lakefile_roots(lakefile: Path) -> List[str]:
    """Names from `roots := #[` in Lean/lakefile.lean (sync with ExportCatalog.lean)."""
    raw = lakefile.read_text(encoding="utf-8", errors="replace")
    m = ROOTS_ASSIGN_RE.search(raw)
    if not m:
        raise ValueError(f"no roots := #[ in {lakefile}")
    chunk = raw[m.end() :]
    end = chunk.find("]")
    if end < 0:
        raise ValueError(f"unclosed roots #[ in {lakefile}")
    chunk = chunk[:end]
    return re.findall(r"`([A-Za-z0-9_]+)`", chunk)


def build_roots_catalog(lean_root: Path) -> Dict[str, Any]:
    lakefile = (lean_root / "lakefile.lean").resolve()
    names = parse_lakefile_roots(lakefile)
    entries = [
        {
            "id": f"{ROOT_PREFIX}.{n}",
            "module": f"{ROOT_PREFIX}.{n}",
            "kind": "root",
            "name": n,
        }
        for n in names
    ]
    return {"version": "1", "entries": entries}


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def module_name(lean_root: Path, path: Path) -> str:
    rel = path.relative_to(lean_root)
    stem = "/".join(rel.with_suffix("").parts)
    return stem.replace("/", ".")


def scan_file(path: Path, *, lean_root: Path) -> Dict[str, Any]:
    raw = path.read_bytes()
    text = raw.decode("utf-8", errors="replace")

    declarations: Dict[str, List[str]] = {}
    for kind, name in DECL_RE.findall(text):
        declarations.setdefault(kind, []).append(name)

    imports: List[str] = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped.startswith("import"):
            continue
        if IMPORT_RE.match(line):
            imports.append(line.split(maxsplit=1)[1].strip())

    rel_path = path.resolve().relative_to(lean_root.resolve()).as_posix()
    blob = dict(
        path=rel_path,
        content_sha256=sha256_hex(raw),
        declarations=declarations,
        import_lines=sorted(set(imports)),
    )
    return blob


def build_catalog(lean_root: Path) -> Dict[str, Any]:
    lean_root = lean_root.resolve()
    modules = []
    for p in sorted(lean_root.rglob("*.lean")):
        parts = set(p.parts)
        if ".lake" in parts or "lake-packages" in parts:
            continue
        if p.name.lower().startswith(".#"):
            continue
        blob = scan_file(p, lean_root=lean_root)
        blob["module"] = module_name(lean_root, p)
        modules.append(blob)

    edges = []
    for mod in modules:
        src_module = mod["module"]
        for imp in mod["import_lines"]:
            tgt = strip_import_to_module(imp)
            edges.append({"from": src_module, "import": imp, "to_approx": tgt})

    catalog_body = dict(
        version=1,
        lean_root="Lean",
        toolchain_hint="Lean/lake-toolchain (+ mathlib pinned in lakefile.lean)",
        modules=modules,
        module_graph_edges=edges,
    )

    canon = json.dumps(catalog_body, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    catalog_body["digest"] = sha256_hex(canon.encode("utf-8"))
    return catalog_body


def write_catalog_lock(lock_path: Path, catalog: Dict[str, Any]) -> None:
    """Emit pin metadata beside catalog.json (digest + module_count)."""
    lock_body = dict(
        version=1,
        role="lean_catalog_lock",
        catalog_path="artifacts/catalog.json",
        catalog_digest_hex=catalog["digest"],
        module_count=len(catalog.get("modules", [])),
        notes=(
            "Canonical digest from tools/lean_export/export_catalog.py "
            "(SHA-256 of JSON body before the digest key). Regenerate with: make lean-catalog-export"
        ),
    )
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("w", encoding="utf-8") as f:
        json.dump(lock_body, f, indent=2)
        f.write("\n")


def strip_import_to_module(import_line_tail: str) -> str:
    """
    Rough normalisation — leaves Mathlib-style chains as dotted names without resolution.
    """
    s = import_line_tail.strip()
    s = s.replace("«", "").replace("»", "")
    return s.replace(" ", "")


def module_basename(module: str) -> str:
    """Last dotted segment — used for rough cross-repo overlap (not Mathlib-resolved)."""
    return module.rsplit(".", 1)[-1]


def tag_catalog_modules(catalog: Dict[str, Any], repo_tag: str) -> List[Dict[str, Any]]:
    tagged = []
    for mod in catalog.get("modules", []):
        row = dict(mod)
        row["repo"] = repo_tag
        tagged.append(row)
    return tagged


def approve_cross_repo_merge() -> bool:
    """True when operator explicitly approves writing a unified catalog pin."""
    return os.environ.get(APPROVE_CROSS_REPO_MERGE_ENV) == "1"


def merge_catalog_modules(
    primary: Dict[str, Any],
    secondary: Dict[str, Any],
    *,
    primary_repo: str,
    secondary_repo: str,
) -> List[Dict[str, Any]]:
    """Merge module rows; primary wins on basename overlap (last path segment)."""
    merged: List[Dict[str, Any]] = []
    seen_bases: set[str] = set()

    for mod in primary.get("modules", []):
        row = dict(mod)
        row["repo"] = primary_repo
        merged.append(row)
        seen_bases.add(module_basename(mod["module"]))

    for mod in secondary.get("modules", []):
        base = module_basename(mod["module"])
        if base in seen_bases:
            continue
        row = dict(mod)
        row["repo"] = secondary_repo
        merged.append(row)

    return sorted(merged, key=lambda m: (m.get("repo", ""), m.get("module", "")))


def build_module_graph_edges(modules: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    edges = []
    for mod in modules:
        src_module = mod["module"]
        for imp in mod.get("import_lines", []):
            tgt = strip_import_to_module(imp)
            edges.append({"from": src_module, "import": imp, "to_approx": tgt})
    return edges


def build_merged_catalog(
    primary: Dict[str, Any],
    secondary: Dict[str, Any],
    *,
    primary_repo: str,
    secondary_repo: str,
) -> Dict[str, Any]:
    """Unified catalog body (digest over pre-digest JSON, same as build_catalog)."""
    merged_modules = merge_catalog_modules(
        primary,
        secondary,
        primary_repo=primary_repo,
        secondary_repo=secondary_repo,
    )
    catalog_body = dict(
        version=1,
        lean_root=primary.get("lean_root"),
        lean_roots=[primary.get("lean_root"), secondary.get("lean_root")],
        cross_repo_merge=True,
        primary_repo=primary_repo,
        secondary_repo=secondary_repo,
        modules=merged_modules,
        module_graph_edges=build_module_graph_edges(merged_modules),
    )
    canon = json.dumps(catalog_body, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    catalog_body["digest"] = sha256_hex(canon.encode("utf-8"))
    return catalog_body


def overlap_module_rows(
    primary: Dict[str, Any],
    secondary: Dict[str, Any],
    *,
    primary_repo: str,
    secondary_repo: str,
) -> List[Dict[str, Any]]:
    primary_by_base = {module_basename(m["module"]): m for m in primary.get("modules", [])}
    secondary_by_base = {module_basename(m["module"]): m for m in secondary.get("modules", [])}
    overlap = sorted(set(primary_by_base) & set(secondary_by_base))
    rows = []
    for base in overlap:
        rows.append(
            dict(
                basename=base,
                primary_module=primary_by_base[base]["module"],
                secondary_module=secondary_by_base[base]["module"],
                winner_repo=primary_repo,
                secondary_repo=secondary_repo,
            )
        )
    return rows


def build_cross_repo_preview(
    primary: Dict[str, Any],
    secondary: Dict[str, Any],
    *,
    primary_repo: str,
    secondary_repo: str,
    approved: bool,
) -> Dict[str, Any]:
    """
    Compare inventories; include unified module list with per-row repo tags.
    When approved=False, catalog.json / catalog.lock.json stay primary-only unless env approves merge.
    """
    primary_by_base = {module_basename(m["module"]): m for m in primary.get("modules", [])}
    secondary_by_base = {module_basename(m["module"]): m for m in secondary.get("modules", [])}

    only_primary = sorted(set(primary_by_base) - set(secondary_by_base))
    only_secondary = sorted(set(secondary_by_base) - set(primary_by_base))
    overlap = sorted(set(primary_by_base) & set(secondary_by_base))
    merged_modules = merge_catalog_modules(
        primary,
        secondary,
        primary_repo=primary_repo,
        secondary_repo=secondary_repo,
    )
    merged_catalog = build_merged_catalog(
        primary,
        secondary,
        primary_repo=primary_repo,
        secondary_repo=secondary_repo,
    )

    if approved:
        notes = (
            f"{APPROVE_CROSS_REPO_MERGE_ENV}=1 — unified catalog may be written to "
            "artifacts/catalog.json and catalog.lock.json (not this preview file); "
            "bump manifold upstream_catalog_digest_hex."
        )
    else:
        notes = (
            "Preview only — does not update artifacts/catalog.json or catalog.lock.json. "
            f"Set {APPROVE_CROSS_REPO_MERGE_ENV}=1 to write unified catalog (primary wins basename overlap)."
        )

    return dict(
        version=1,
        role="lean_catalog_cross_repo_preview",
        # Preview JSON is never a production pin; dry_run stays true even when merge is approved.
        dry_run=True,
        approve_cross_repo_merge_env=APPROVE_CROSS_REPO_MERGE_ENV,
        approve_cross_repo_merge_set=approved,
        merge_blocked=not approved,
        notes=notes,
        primary_repo=primary_repo,
        secondary_repo=secondary_repo,
        primary_lean_root=primary.get("lean_root"),
        secondary_lean_root=secondary.get("lean_root"),
        primary_module_count=len(primary.get("modules", [])),
        secondary_module_count=len(secondary.get("modules", [])),
        merged_module_count=len(merged_modules),
        primary_digest_hex=primary.get("digest"),
        secondary_digest_hex=secondary.get("digest"),
        merged_digest_hex=merged_catalog.get("digest"),
        overlap_basename_count=len(overlap),
        only_in_primary_basename=only_primary,
        only_in_secondary_basename=only_secondary,
        overlap_basename=overlap,
        overlap_modules=overlap_module_rows(
            primary,
            secondary,
            primary_repo=primary_repo,
            secondary_repo=secondary_repo,
        ),
        modules=merged_modules,
        modules_primary=tag_catalog_modules(primary, primary_repo),
        modules_secondary=tag_catalog_modules(secondary, secondary_repo),
    )


def write_cross_repo_preview(preview_path: Path, preview: Dict[str, Any]) -> None:
    preview_path.parent.mkdir(parents=True, exist_ok=True)
    with preview_path.open("w", encoding="utf-8") as f:
        json.dump(preview, f, indent=2)
        f.write("\n")


def main() -> None:
    parser = argparse.ArgumentParser(description="Export Lean catalog metadata to JSON.")
    parser.add_argument(
        "--lean-root",
        type=Path,
        default=Path("Lean"),
        help="Directory containing UMST.DoubleSlit sources (contains lakefile).",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("artifacts/catalog.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--roots-only",
        action="store_true",
        help="Emit compact Lake-style {version, entries} to --roots-out (does not touch catalog.lock.json).",
    )
    parser.add_argument(
        "--roots-out",
        type=Path,
        default=Path("artifacts/catalog-roots.json"),
        help="Output for --roots-only (Lake exe schema; not used for drift pins).",
    )
    parser.add_argument(
        "--also-lean-root",
        type=Path,
        default=None,
        help=(
            "Optional second Lean tree (e.g. ../umst-formal/Lean). "
            "Writes cross-repo preview; merges into catalog.json only when "
            f"{APPROVE_CROSS_REPO_MERGE_ENV}=1 (unless --cross-repo-only)."
        ),
    )
    parser.add_argument(
        "--also-lean-repo-tag",
        type=str,
        default="umst-formal",
        help="Repo label for --also-lean-root modules (default: umst-formal).",
    )
    parser.add_argument(
        "--primary-repo-tag",
        type=str,
        default="umst-formal-double-slit",
        help="Repo label for --lean-root modules in cross-repo preview.",
    )
    parser.add_argument(
        "--cross-repo-preview-out",
        type=Path,
        default=Path("artifacts/catalog-cross-repo-preview.json"),
        help="Dry-run JSON when --also-lean-root is set (not used for CI pins).",
    )
    parser.add_argument(
        "--cross-repo-only",
        action="store_true",
        help=(
            "With --also-lean-root: emit preview only; do not write catalog.json or catalog.lock.json."
        ),
    )
    args = parser.parse_args()
    lean_root = args.lean_root.expanduser().resolve()

    if args.roots_only:
        roots_doc = build_roots_catalog(lean_root)
        args.roots_out.parent.mkdir(parents=True, exist_ok=True)
        with args.roots_out.open("w", encoding="utf-8") as f:
            json.dump(roots_doc, f, indent=2)
            f.write("\n")
        print(f"Wrote {args.roots_out.resolve()} entries={len(roots_doc.get('entries', []))}")
        return

    also_root = args.also_lean_root.expanduser().resolve() if args.also_lean_root else None
    catalog: Dict[str, Any] | None = None
    if also_root is not None:
        if not also_root.is_dir():
            raise SystemExit(f"--also-lean-root not a directory: {also_root}")
        primary_catalog = build_catalog(lean_root)
        secondary_catalog = build_catalog(also_root)
        approved = approve_cross_repo_merge()
        preview = build_cross_repo_preview(
            primary_catalog,
            secondary_catalog,
            primary_repo=args.primary_repo_tag,
            secondary_repo=args.also_lean_repo_tag,
            approved=approved,
        )
        write_cross_repo_preview(args.cross_repo_preview_out, preview)
        preview_label = "cross-repo preview" if not approved else "cross-repo preview (merge approved)"
        print(
            f"{preview_label} → {args.cross_repo_preview_out.resolve()} "
            f"primary={preview['primary_module_count']} "
            f"secondary={preview['secondary_module_count']} "
            f"merged={preview['merged_module_count']} "
            f"only_in_{args.also_lean_repo_tag}={len(preview['only_in_secondary_basename'])} "
            f"approve_set={approved}"
        )
        if args.cross_repo_only:
            print("Skipped catalog.json / catalog.lock.json (--cross-repo-only).")
            return
        if approved:
            catalog = build_merged_catalog(
                primary_catalog,
                secondary_catalog,
                primary_repo=args.primary_repo_tag,
                secondary_repo=args.also_lean_repo_tag,
            )
        else:
            catalog = primary_catalog

    if catalog is None:
        catalog = build_catalog(lean_root)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", encoding="utf-8") as f:
        json.dump(catalog, f, indent=2)
        f.write("\n")

    lock_path = args.out.parent / "catalog.lock.json"
    write_catalog_lock(lock_path, catalog)

    digest = catalog.get("digest", "")
    print(f"Wrote {args.out.resolve()} digest={digest}")
    print(f"Wrote {lock_path.resolve()} module_count={len(catalog.get('modules', []))}")
    if also_root is not None:
        if approve_cross_repo_merge():
            print(
                f"Unified cross-repo catalog written ({APPROVE_CROSS_REPO_MERGE_ENV}=1). "
                "Bump umst-manifold upstream_catalog_digest_hex before CI."
            )
        else:
            print(
                f"Canonical digest is primary-only; set {APPROVE_CROSS_REPO_MERGE_ENV}=1 "
                "to write unified catalog.json / catalog.lock.json."
            )


if __name__ == "__main__":
    main()
