SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
# Lean catalog export: canonical CI path

Comparison of **`lake exe export_catalog`** (Lean `ExportCatalog`) vs **`tools/lean_export/export_catalog.py`** for `umst-formal-double-slit`, recorded **2026-05-21** on macOS with Lake **5.0.0** / Lean **4.29.1**.

## Commands (from repository root)

| Path | Command | Output |
|------|---------|--------|
| Lake (preferred) | `cd Lean && lake exe export_catalog` | `artifacts/catalog.json` |
| Lake fallback (native `dyld` failure) | `cd Lean && lake build ExportCatalog && lake env lean ../tools/lean_export/ExportCatalogSmoke.lean` | same |
| Python | `make lean-catalog-export` or `python3 tools/lean_export/export_catalog.py --lean-root Lean --out artifacts/catalog.json` | `artifacts/catalog.json` + `artifacts/catalog.lock.json` |

**Note:** On this host, `lake exe export_catalog` exited **134** (`dyld`: `__DATA_CONST segment missing SG_READ_ONLY flag`). The smoke fallback succeeded and produced the same JSON shape as the executable’s `main`.

## Summary table

| Metric | `lake exe export_catalog` | `export_catalog.py` |
|--------|---------------------------|---------------------|
| **Module / entry count** | **59** (`entries[]`, Lake `roots`) | **69** (all `Lean/**/*.lean` except `.lake/`) |
| **Digest in JSON** | **None** (no `digest` field) | **`c1d9ba2aa402106a3477f454dd6d28015eb399c1160d8a2e2ba7d16788fdbfcc`** (SHA-256 of canonical JSON body *before* adding `digest`) |
| **Lock file** | Does not write `catalog.lock.json` | Writes `artifacts/catalog.lock.json` (`module_count`: 69, `catalog_digest_hex` above) |
| **JSON top-level** | `version` (string), `entries` | `version` (int), `lean_root`, `toolchain_hint`, `modules`, `module_graph_edges`, `digest` |
| **Entry identity** | `UMST.DoubleSlit.<RootName>`, `kind`: `root` | File-path module names (e.g. `UMSTCore`, `TestEntropy`, `lakefile`) + per-file `content_sha256`, declarations, imports |

## Missing modules (set difference)

Interpretation uses **short names** (filename stem). Lake list = pinned `roots` in `Lean/lakefile.lean` / `ExportCatalog.lean`. Python list = every `*.lean` under `Lean/`.

### In Python scan, **not** in Lake `entries` (10) — expected exclusions

These exist on disk but are **not** default Lake `roots` (see `Lean/lakefile.lean` comment block):

- `FlashMoERuntimeScaffold`
- `LogSum`
- `MatrixLog`
- `Test3`, `Test4`, `TestEntropy`, `TestFixes`, `TestMixed`
- `lakefile` (package config, not a proof module)
- `test_tensor_eigen`

### In Lake `entries`, **not** in Python scan

**None** — all 59 pinned roots have a matching top-level `Lean/<Name>.lean` file.

### `ExportCatalog.lean` vs emitted Lake JSON

`pinnedRootNames` length **59**; smoke/`lake exe` output **59** entries — **in sync**.

## Path collision (important)

Both exporters default to **`artifacts/catalog.json`**. They emit **incompatible schemas**. Running one after the other **overwrites** the other format. `artifacts/catalog.lock.json` is only updated by the **Python** exporter and always describes the **Python** digest.

Downstream **`umst-manifold`** pins the Python digest via `artifacts/catalog.lock.json` / `UMST_CATALOG` (see manifold `build.rs`, `docs/CATALOG_ROW_COUNT.md`).

## CI recommendation

| Concern | Canonical exporter |
|---------|-------------------|
| **Digest pin, module graph, Rust/manifold CI** | **`export_catalog.py`** via **`make lean-catalog-export`** |
| **Default Lake build boundary (`roots`)** | **`lake exe export_catalog`** (or smoke fallback) — treat as a **roots manifest check**, not a substitute for the Python lock |

### Rationale

1. **Committed lock and manifold builds** already assume the Python catalog: digest `c1d9ba…`, **69** modules (`catalog.lock.json`).
2. **Lake export** answers “what does `lake build` include by default?” (**59** roots) and stays aligned with `lakefile.lean` when `pinnedRootNames` is maintained.
3. **Do not** gate manifold digest CI on `lake exe` alone without splitting output paths (e.g. `artifacts/catalog-roots.json` for Lake, keep `artifacts/catalog.json` + `catalog.lock.json` for Python).

### Suggested CI layout (future hardening)

```bash
# Pin / drift (canonical today)
make lean-catalog-export
# Optional: assert lock digest unchanged or update lock in a dedicated PR

# Roots parity (non-destructive)
cd Lean && lake build ExportCatalog && lake env lean ../tools/lean_export/ExportCatalogSmoke.lean
# Compare artifacts/catalog-roots.json if split; today compare entry count == 59 vs lakefile roots
```

## Regeneration checklist (Lean churn)

1. `make lean-catalog-export` — refresh `artifacts/catalog.json` and `artifacts/catalog.lock.json`.
2. Copy or promote `catalog_digest_hex` / `module_count` into `umst-manifold/artifacts/catalog.lock.json` when manifold should track the new formal export.
3. Update `tools/lean_export/ExportCatalog.lean` `pinnedRootNames` whenever `Lean/lakefile.lean` `roots` changes; run Lake export (or smoke) and verify **59** (or new count) matches `lakefile.lean`.

## References

- `tools/lean_export/README.md` — schema and maintenance
- `Lean/lakefile.lean` — documents both exporters
- `umst-manifold/docs/TODO_COMPLETION.md` — notes CI drift uses Python scan today
